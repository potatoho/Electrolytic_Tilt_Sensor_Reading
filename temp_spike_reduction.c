#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/gpio.h>
#include <linux/spi/spidev.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define GPIO_CHIP          "/dev/gpiochip0"
#define GPIO_ADC_CS1       22U
#define GPIO_ADC_CS2       23U
#define GPIO_ADC_DRDY      24U

#define SPI_DEVICE         "/dev/spidev0.0"
#define SPI_SPEED_HZ       2000000U

#define PWM_PERIOD_US       1000ULL
#define HALF_PERIOD_US       500ULL
#define EXTERNAL_SETTLING_US 200U
#define DRDY_TIMEOUT_US      250U
#define PWM_EDGE_TIMEOUT_US 3000U
#define REPORT_INTERVAL_US   1000000ULL

#define LPF_TAU_SECONDS       5.0

/*
 * Motion-aware spike guard applied to the 1 s averaged VDIFF before
 * the existing 5 s LPF.
 *
 * Jump candidate threshold:
 *   |raw - guarded| > 350 uV
 *
 * 8-point (~8 s) trend:
 *   motion is accepted only when linear slope and net displacement
 *   have the same direction as the current deviation.
 *
 * Direction-dependent slew limits use about 2x the maximum measured
 * post-LPF motion speed.
 */
#define GUARD_WINDOW_SIZE              8U
#define GUARD_JUMP_THRESHOLD_UV      350.0
#define GUARD_MIN_SLOPE_UV_PER_S      50.0
#define GUARD_MIN_NET_CHANGE_UV       300.0

#define CH1_GUARD_MAX_FALL_UV_PER_S   250.0
#define CH1_GUARD_MAX_RISE_UV_PER_S   100.0
#define CH2_GUARD_MAX_FALL_UV_PER_S   350.0
#define CH2_GUARD_MAX_RISE_UV_PER_S   200.0

#define TCP_MAX_CLIENTS        8
#define TCP_RX_BUFFER_SIZE    128

/* Raspberry Pi 4 / BCM2711 peripheral addresses. */
#define GPIO_BASE_PHYS     0xFE200000UL
#define PWM_BASE_PHYS      0xFE20C000UL
#define CLK_BASE_PHYS      0xFE101000UL
#define PERIPHERAL_SIZE    4096UL

#define GPFSEL1            1U
#define GPLEV0             (0x34U / 4U)
#define PWM_CTL            0U
#define PWM_STA            1U
#define PWM_RNG1           4U
#define PWM_DAT1           5U
#define PWM_RNG2           8U
#define PWM_DAT2           9U
#define CM_PWMCTL          (0xA0U / 4U)
#define CM_PWMDIV          (0xA4U / 4U)

#define CM_PASSWORD        0x5A000000U
#define CM_CTL_SRC_OSC     0x00000001U
#define CM_CTL_ENAB        0x00000010U
#define CM_CTL_KILL        0x00000020U
#define CM_CTL_BUSY        0x00000080U

#define PWM_CTL_PWEN1      (1U << 0)
#define PWM_CTL_MSEN1      (1U << 7)
#define PWM_CTL_PWEN2      (1U << 8)
#define PWM_CTL_POLA2      (1U << 12)
#define PWM_CTL_MSEN2      (1U << 15)

/* 54 MHz oscillator / 54 / 1000 = 1 kHz. */
#define PWM_CLOCK_DIVIDER  54U
#define PWM_RANGE          1000U
#define PWM_DUTY           500U

#define ADS_CMD_RESET      0x06U
#define ADS_CMD_START      0x08U
#define ADS_CMD_RDATA      0x12U
#define ADS_CMD_RREG       0x20U
#define ADS_CMD_WREG       0x40U

#define ADS_REG_ID         0x00U
#define ADS_REG_MODE0      0x02U
#define ADS_REG_MODE1      0x03U
#define ADS_REG_MODE3      0x05U
#define ADS_REG_MODE4      0x10U

#define ADS_MODE0_40000SPS          0x80U
#define ADS_MODE1_CONTINUOUS_DELAY_50US  0x01U
#define ADS_MODE3_STATUS_OFF       0x00U
#define ADS_MODE4_MUX_AIN1_AINCOM  0x20U
#define ADS_MODE4_MUX_AIN0_AINCOM  0x30U
#define ADS_MODE4_GAIN_1            0x04U

#define ADS_CODE_FS        8388608LL
#define ADS_VREF_UV        5000000LL
#define ADS_GAIN_NUM       1LL
#define ADS_GAIN_DEN       1LL

/* 1 degree = 400 mV = 400 uV/mdeg */
#define SENSOR_UV_PER_MDEG 400.0

/* Final angle offset correction [mdeg].
 * Change only these two values when zero-point correction is required.
 * corrected angle = fitted angle + offset
 */
static double offset_ch1 = 0.0;
static double offset_ch2 = 0.0;

struct gpio_group {
    int fd;
    unsigned int count;
};

struct channel_state {
    int32_t high_raw;
    int32_t low_raw;

    int64_t high_sum;
    int64_t low_sum;
    int64_t vcm_sum;
    int64_t vdiff_sum;

    uint32_t sample_count;
};

struct guard_state {
    double corrected_uv;
    double lpf_uv;
    double history_uv[GUARD_WINDOW_SIZE];
    double history_t[GUARD_WINDOW_SIZE];
    unsigned int history_count;
    unsigned int history_pos;
    int initialized;
};

static volatile sig_atomic_t running = 1;

static int spi_fd = -1;
static struct gpio_group chip_select = {-1, 0};
static struct gpio_group drdy = {-1, 0};
static volatile uint32_t *gpio_regs;
static volatile uint32_t *pwm_regs;
static volatile uint32_t *clk_regs;
static uint32_t saved_gpfsel1;
static int pwm_gpio_configured;

static void on_signal(int signo)
{
    (void)signo;
    running = 0;
}

static uint64_t monotonic_us(void)
{
    struct timespec ts;

    clock_gettime(CLOCK_MONOTONIC, &ts);

    return (uint64_t)ts.tv_sec * 1000000ULL +
           (uint64_t)ts.tv_nsec / 1000ULL;
}

static void sleep_until_us(uint64_t deadline_us)
{
    struct timespec ts = {
        .tv_sec = (time_t)(deadline_us / 1000000ULL),
        .tv_nsec = (long)((deadline_us % 1000000ULL) * 1000ULL)
    };

    int rc;

    do {
        rc = clock_nanosleep(
            CLOCK_MONOTONIC,
            TIMER_ABSTIME,
            &ts,
            NULL
        );
    } while (rc == EINTR && running);
}

static void peripheral_barrier(void)
{
    __sync_synchronize();
}

static int pwm1_level(void)
{
    return (gpio_regs[GPLEV0] & (1U << 18)) != 0U;
}

static int wait_pwm_edge(
    int from_level,
    int to_level,
    uint64_t *edge_us)
{
    uint64_t deadline = monotonic_us() + PWM_EDGE_TIMEOUT_US;
    int saw_from = 0;

    while (running && monotonic_us() < deadline) {
        int level = pwm1_level();

        if (level == from_level) {
            saw_from = 1;
        } else if (saw_from && level == to_level) {
            *edge_us = monotonic_us();
            return 0;
        }
    }

    return -1;
}

static void *map_peripheral(int mem_fd, off_t address)
{
    void *mapped = mmap(NULL, PERIPHERAL_SIZE,
                        PROT_READ | PROT_WRITE, MAP_SHARED,
                        mem_fd, address);

    if (mapped == MAP_FAILED) {
        perror("mmap");
        return NULL;
    }

    return mapped;
}

static int wait_pwm_clock(int expected_busy)
{
    for (unsigned int i = 0; i < 1000000U; ++i) {
        int busy = (clk_regs[CM_PWMCTL] & CM_CTL_BUSY) != 0;
        if (busy == expected_busy)
            return 0;
    }
    return -1;
}

static int start_hardware_pwm(uint64_t *epoch_us)
{
    int mem_fd = open("/dev/mem", O_RDWR | O_SYNC | O_CLOEXEC);

    if (mem_fd < 0) {
        perror("/dev/mem (run as root)");
        return -1;
    }

    gpio_regs = map_peripheral(mem_fd, GPIO_BASE_PHYS);
    pwm_regs = map_peripheral(mem_fd, PWM_BASE_PHYS);
    clk_regs = map_peripheral(mem_fd, CLK_BASE_PHYS);
    close(mem_fd);

    if (gpio_regs == NULL || pwm_regs == NULL || clk_regs == NULL)
        return -1;

    saved_gpfsel1 = gpio_regs[GPFSEL1];
    uint32_t fsel = saved_gpfsel1;
    fsel &= ~((7U << 24) | (7U << 27));
    fsel |= (2U << 24) | (2U << 27); /* GPIO18/19 ALT5 */
    gpio_regs[GPFSEL1] = fsel;
    peripheral_barrier();
    pwm_gpio_configured = 1;

    pwm_regs[PWM_CTL] = 0;
    clk_regs[CM_PWMCTL] = CM_PASSWORD | CM_CTL_KILL;
    peripheral_barrier();

    if (wait_pwm_clock(0) < 0) {
        fprintf(stderr, "PWM clock did not stop\n");
        return -1;
    }

    clk_regs[CM_PWMDIV] = CM_PASSWORD | (PWM_CLOCK_DIVIDER << 12);
    clk_regs[CM_PWMCTL] =
        CM_PASSWORD | CM_CTL_SRC_OSC | CM_CTL_ENAB;
    peripheral_barrier();

    if (wait_pwm_clock(1) < 0) {
        fprintf(stderr, "PWM clock did not start\n");
        return -1;
    }

    pwm_regs[PWM_STA] = 0x01FCU;
    pwm_regs[PWM_RNG1] = PWM_RANGE;
    usleep(10);
    pwm_regs[PWM_DAT1] = PWM_DUTY;
    pwm_regs[PWM_RNG2] = PWM_RANGE;
    usleep(10);
    pwm_regs[PWM_DAT2] = PWM_DUTY;
    peripheral_barrier();

    /* One write starts both channels; channel 2 is polarity-inverted. */
    pwm_regs[PWM_CTL] =
        PWM_CTL_PWEN1 | PWM_CTL_MSEN1 |
        PWM_CTL_PWEN2 | PWM_CTL_POLA2 | PWM_CTL_MSEN2;
    peripheral_barrier();

    *epoch_us = monotonic_us();
    return 0;
}

static void stop_hardware_pwm(void)
{
    if (pwm_regs != NULL) {
        pwm_regs[PWM_CTL] = 0;
        peripheral_barrier();
    }
    if (gpio_regs != NULL && pwm_gpio_configured) {
        gpio_regs[GPFSEL1] = saved_gpfsel1;
        peripheral_barrier();
    }
    if (gpio_regs != NULL)
        munmap((void *)gpio_regs, PERIPHERAL_SIZE);
    if (pwm_regs != NULL)
        munmap((void *)pwm_regs, PERIPHERAL_SIZE);
    if (clk_regs != NULL)
        munmap((void *)clk_regs, PERIPHERAL_SIZE);

    gpio_regs = NULL;
    pwm_regs = NULL;
    clk_regs = NULL;
    pwm_gpio_configured = 0;
}

static int gpio_request(
    int chip_fd,
    const unsigned int *offsets,
    unsigned int count,
    uint64_t flags,
    uint64_t initial_bits,
    const char *consumer,
    struct gpio_group *group)
{
    struct gpio_v2_line_request req;

    memset(&req, 0, sizeof(req));

    for (unsigned int i = 0; i < count; ++i)
        req.offsets[i] = offsets[i];

    req.num_lines = count;
    req.config.flags = flags;

    snprintf(
        req.consumer,
        sizeof(req.consumer),
        "%s",
        consumer
    );

    if (flags & GPIO_V2_LINE_FLAG_OUTPUT) {
        req.config.num_attrs = 1;

        req.config.attrs[0].attr.id =
            GPIO_V2_LINE_ATTR_ID_OUTPUT_VALUES;

        req.config.attrs[0].attr.values = initial_bits;
        req.config.attrs[0].mask = (1ULL << count) - 1ULL;
    }

    if (ioctl(chip_fd, GPIO_V2_GET_LINE_IOCTL, &req) < 0) {
        perror("GPIO_V2_GET_LINE_IOCTL");
        return -1;
    }

    group->fd = req.fd;
    group->count = count;

    return 0;
}

static int gpio_set(
    const struct gpio_group *group,
    uint64_t bits)
{
    struct gpio_v2_line_values values = {
        .bits = bits,
        .mask = (1ULL << group->count) - 1ULL
    };

    return ioctl(
        group->fd,
        GPIO_V2_LINE_SET_VALUES_IOCTL,
        &values
    );
}

static int gpio_get(const struct gpio_group *group)
{
    struct gpio_v2_line_values values = {
        .bits = 0,
        .mask = 1
    };

    if (ioctl(
            group->fd,
            GPIO_V2_LINE_GET_VALUES_IOCTL,
            &values) < 0) {
        return -1;
    }

    return (int)(values.bits & 1ULL);
}

static int select_cs(unsigned int cs)
{
    return gpio_set(
        &chip_select,
        cs == 1U ? 0x2ULL : 0x1ULL
    );
}

static void deselect_cs(void)
{
    (void)gpio_set(&chip_select, 0x3ULL);
}

static uint8_t ads_crc8(
    const uint8_t *data,
    size_t len)
{
    uint8_t crc = 0xFFU;

    for (size_t i = 0; i < len; ++i) {
        crc ^= data[i];

        for (unsigned int bit = 0; bit < 8; ++bit) {
            crc = (crc & 0x80U)
                ? (uint8_t)((crc << 1) ^ 0x07U)
                : (uint8_t)(crc << 1);
        }
    }

    return crc;
}

static int spi_transfer(
    const uint8_t *tx,
    uint8_t *rx,
    size_t len)
{
    struct spi_ioc_transfer tr;

    memset(&tr, 0, sizeof(tr));

    tr.tx_buf = (uintptr_t)tx;
    tr.rx_buf = (uintptr_t)rx;
    tr.len = (uint32_t)len;
    tr.speed_hz = SPI_SPEED_HZ;
    tr.bits_per_word = 8;

    return ioctl(
        spi_fd,
        SPI_IOC_MESSAGE(1),
        &tr
    ) < 0 ? -1 : 0;
}

static int ads_transaction(
    unsigned int cs,
    const uint8_t *tx,
    uint8_t *rx,
    size_t len)
{
    if (select_cs(cs) < 0)
        return -1;

    int rc = spi_transfer(tx, rx, len);

    deselect_cs();

    return rc;
}

static int ads_command(uint8_t command)
{
    uint8_t tx[4] = {command, 0, 0, 0};
    uint8_t rx[4] = {0};

    tx[2] = ads_crc8(tx, 2);

    if (ads_transaction(1, tx, rx, sizeof(tx)) < 0)
        return -1;

    return rx[3] == tx[2] ? 0 : -1;
}

static int ads_read_reg(
    uint8_t address,
    uint8_t *value)
{
    uint8_t tx[6] = {0};
    uint8_t rx[6] = {0};

    tx[0] = ADS_CMD_RREG | (address & 0x1FU);
    tx[2] = ads_crc8(tx, 2);

    unsigned int cs = address >= 0x10U ? 2U : 1U;

    if (ads_transaction(cs, tx, rx, sizeof(tx)) < 0)
        return -1;

    if (rx[3] != tx[2])
        return -1;

    if (rx[5] != ads_crc8(&rx[4], 1))
        return -1;

    *value = rx[4];

    return 0;
}

static int ads_write_reg(
    uint8_t address,
    uint8_t value)
{
    uint8_t tx[4] = {
        ADS_CMD_WREG | (address & 0x1FU),
        value,
        0,
        0
    };

    uint8_t rx[4] = {0};

    tx[2] = ads_crc8(tx, 2);

    unsigned int cs = address >= 0x10U ? 2U : 1U;

    if (ads_transaction(cs, tx, rx, sizeof(tx)) < 0)
        return -1;

    return rx[3] == tx[2] ? 0 : -1;
}

static int ads_read_data(int32_t *code)
{
    uint8_t tx[8] = {
        ADS_CMD_RDATA, 0, 0, 0,
        0, 0, 0, 0
    };

    uint8_t rx[8] = {0};

    tx[2] = ads_crc8(tx, 2);

    if (ads_transaction(1, tx, rx, sizeof(tx)) < 0)
        return -1;

    if (rx[3] != tx[2])
        return -1;

    if (rx[7] != ads_crc8(&rx[4], 3))
        return -1;

    uint32_t raw =
        ((uint32_t)rx[4] << 16) |
        ((uint32_t)rx[5] << 8) |
        (uint32_t)rx[6];

    if (raw & 0x800000UL)
        raw |= 0xFF000000UL;

    *code = (int32_t)raw;

    return 0;
}

static int ads_init(void)
{
    uint8_t id = 0;
    uint8_t mode0 = 0;
    uint8_t mode1 = 0;

    deselect_cs();
    usleep(1000);

    if (ads_command(ADS_CMD_RESET) < 0) {
        fprintf(stderr, "ADS reset failed\n");
        return -1;
    }

    usleep(10000);

    if (ads_read_reg(ADS_REG_ID, &id) < 0 ||
        (id & 0xF0U) != 0x60U) {
        fprintf(
            stderr,
            "ADS ID read failed (ID=0x%02X)\n",
            id
        );
        return -1;
    }

    printf("ADS ID=0x%02X\n", id);

    if (ads_write_reg(
            ADS_REG_MODE3,
            ADS_MODE3_STATUS_OFF) < 0) {
        fprintf(stderr, "ADS MODE3 configuration failed\n");
        return -1;
    }

    if (ads_write_reg(
            ADS_REG_MODE0,
            ADS_MODE0_40000SPS) < 0) {
        fprintf(stderr, "ADS MODE0 configuration failed\n");
        return -1;
    }

    if (ads_write_reg(
            ADS_REG_MODE1,
            ADS_MODE1_CONTINUOUS_DELAY_50US) < 0) {
        fprintf(stderr, "ADS MODE1 configuration failed\n");
        return -1;
    }

    if (ads_read_reg(ADS_REG_MODE0, &mode0) < 0 ||
        mode0 != ADS_MODE0_40000SPS) {
        fprintf(stderr,
                "ADS MODE0 verification failed "
                "(expected=0x%02X, actual=0x%02X)\n",
                ADS_MODE0_40000SPS,
                mode0);
        return -1;
    }

    if (ads_read_reg(ADS_REG_MODE1, &mode1) < 0 ||
        mode1 != ADS_MODE1_CONTINUOUS_DELAY_50US) {
        fprintf(stderr,
                "ADS MODE1 verification failed "
                "(expected=0x%02X, actual=0x%02X)\n",
                ADS_MODE1_CONTINUOUS_DELAY_50US,
                mode1);
        return -1;
    }

    printf("ADS MODE0=0x%02X, MODE1=0x%02X\n",
           mode0,
           mode1);

    if (ads_write_reg(
            ADS_REG_MODE4,
            ADS_MODE4_MUX_AIN0_AINCOM |
            ADS_MODE4_GAIN_1) < 0) {
        fprintf(stderr, "ADS MODE4 configuration failed\n");
        return -1;
    }

    return 0;
}

static int wait_drdy_falling_edge(uint32_t timeout_us)
{
    uint64_t deadline = monotonic_us() + timeout_us;
    int saw_high = 0;

    while (running && monotonic_us() < deadline) {
        int value = gpio_get(&drdy);

        if (value < 0)
            return -1;

        if (value != 0) {
            saw_high = 1;
        } else if (saw_high) {
            return 0;
        }
    }

    return -1;
}

static int ads_select_channel(unsigned int channel)
{
    uint8_t mux = channel == 0U
        ? ADS_MODE4_MUX_AIN0_AINCOM
        : ADS_MODE4_MUX_AIN1_AINCOM;

    return ads_write_reg(
        ADS_REG_MODE4,
        mux | ADS_MODE4_GAIN_1
    );
}

static int retry_ads_select_channel(unsigned int channel)
{
    unsigned int retry_count = 0;

    while (running) {
        if (ads_select_channel(channel) == 0) {
            if (retry_count > 0) {
                fprintf(stderr,
                        "CH%u MUX recovered after %u retries\n",
                        channel + 1U,
                        retry_count);
            }

            return 0;
        }

        retry_count++;

        if (retry_count == 1U ||
            retry_count % 1000U == 0U) {
            fprintf(stderr,
                    "CH%u MUX selection failed; retrying (%u)\n",
                    channel + 1U,
                    retry_count);
        }

        deselect_cs();
        usleep(1000);
    }

    return -1;
}

static int ads_restart_and_read(int32_t *raw)
{
    if (ads_command(ADS_CMD_START) < 0)
        return -1;

    if (wait_drdy_falling_edge(DRDY_TIMEOUT_US) < 0)
        return -1;

    return ads_read_data(raw);
}

static void accumulate_channel(
    struct channel_state *channel)
{
    int64_t high = channel->high_raw;
    int64_t low = channel->low_raw;

    channel->high_sum += high;
    channel->low_sum += low;
    channel->vcm_sum += (high + low) / 2;
    channel->vdiff_sum += (high - low) / 2;
    channel->sample_count++;
}

static void reset_channel_average(
    struct channel_state *channel)
{
    channel->high_sum = 0;
    channel->low_sum = 0;
    channel->vcm_sum = 0;
    channel->vdiff_sum = 0;
    channel->sample_count = 0;
}

static int32_t code_to_uv(int64_t code)
{
    int64_t uv =
        code *
        ADS_VREF_UV *
        ADS_GAIN_DEN;

    uv /= ADS_CODE_FS * ADS_GAIN_NUM;

    return (int32_t)uv;
}

static int read_board_temp_mC(void)
{
    int fd = open(
        "/sys/class/thermal/thermal_zone0/temp",
        O_RDONLY | O_CLOEXEC
    );

    if (fd < 0)
        return -1;

    char buffer[32];
    ssize_t length = read(fd, buffer, sizeof(buffer) - 1U);

    close(fd);

    if (length <= 0)
        return -1;

    buffer[length] = '\0';

    char *end = NULL;
    long value = strtol(buffer, &end, 10);

    if (end == buffer)
        return -1;

    return (int)value;
}

/* Fifth-order calibration: measured angle T [mdeg] -> corrected C [mdeg]. */
static double fit_angle_mdeg(double t)
{
    return ((((-4.20529061e-17 * t
               - 7.57486695e-13) * t
              + 9.26577767e-9) * t
             - 1.15097020e-5) * t
            + 0.916180507) * t
           - 0.568154573;
}

static double clamp_double(double value, double low, double high)
{
    if (value < low)
        return low;
    if (value > high)
        return high;
    return value;
}

static int same_sign_nonzero(double a, double b)
{
    return (a > 0.0 && b > 0.0) || (a < 0.0 && b < 0.0);
}

static void guard_push_history(
    struct guard_state *state,
    double time_s,
    double raw_uv)
{
    state->history_uv[state->history_pos] = raw_uv;
    state->history_t[state->history_pos] = time_s;
    state->history_pos = (state->history_pos + 1U) % GUARD_WINDOW_SIZE;

    if (state->history_count < GUARD_WINDOW_SIZE)
        state->history_count++;
}

static int guard_linear_trend(
    const struct guard_state *state,
    double *slope_uv_per_s,
    double *net_uv)
{
    if (state->history_count < GUARD_WINDOW_SIZE) {
        *slope_uv_per_s = 0.0;
        *net_uv = 0.0;
        return 0;
    }

    unsigned int first = state->history_pos;
    double sum_t = 0.0;
    double sum_y = 0.0;

    for (unsigned int i = 0; i < GUARD_WINDOW_SIZE; ++i) {
        unsigned int idx = (first + i) % GUARD_WINDOW_SIZE;
        sum_t += state->history_t[idx];
        sum_y += state->history_uv[idx];
    }

    double mean_t = sum_t / (double)GUARD_WINDOW_SIZE;
    double mean_y = sum_y / (double)GUARD_WINDOW_SIZE;
    double num = 0.0;
    double den = 0.0;

    for (unsigned int i = 0; i < GUARD_WINDOW_SIZE; ++i) {
        unsigned int idx = (first + i) % GUARD_WINDOW_SIZE;
        double dt_local = state->history_t[idx] - mean_t;
        double dy = state->history_uv[idx] - mean_y;
        num += dt_local * dy;
        den += dt_local * dt_local;
    }

    if (den <= 0.0) {
        *slope_uv_per_s = 0.0;
        *net_uv = 0.0;
        return 0;
    }

    unsigned int last =
        (state->history_pos + GUARD_WINDOW_SIZE - 1U) % GUARD_WINDOW_SIZE;

    *slope_uv_per_s = num / den;
    *net_uv = state->history_uv[last] - state->history_uv[first];

    return 1;
}

static double guard_update(
    struct guard_state *state,
    double time_s,
    double raw_uv,
    double dt,
    double max_fall_uv_per_s,
    double max_rise_uv_per_s)
{
    if (dt <= 0.0)
        dt = 1.0;

    if (!state->initialized) {
        state->corrected_uv = raw_uv;
        state->lpf_uv = raw_uv;
        state->initialized = 1;
        guard_push_history(state, time_s, raw_uv);
        return state->corrected_uv;
    }

    guard_push_history(state, time_s, raw_uv);

    double slope_uv_per_s = 0.0;
    double net_uv = 0.0;
    int have_trend =
        guard_linear_trend(state, &slope_uv_per_s, &net_uv);

    double delta_uv = raw_uv - state->corrected_uv;
    int allow_follow = 1;

    if (delta_uv > GUARD_JUMP_THRESHOLD_UV ||
        delta_uv < -GUARD_JUMP_THRESHOLD_UV) {
        int trend_is_motion =
            have_trend &&
            (slope_uv_per_s >= GUARD_MIN_SLOPE_UV_PER_S ||
             slope_uv_per_s <= -GUARD_MIN_SLOPE_UV_PER_S) &&
            (net_uv >= GUARD_MIN_NET_CHANGE_UV ||
             net_uv <= -GUARD_MIN_NET_CHANGE_UV) &&
            same_sign_nonzero(slope_uv_per_s, net_uv) &&
            same_sign_nonzero(slope_uv_per_s, delta_uv);

        if (!trend_is_motion)
            allow_follow = 0;
    }

    if (allow_follow) {
        double max_fall_step_uv = max_fall_uv_per_s * dt;
        double max_rise_step_uv = max_rise_uv_per_s * dt;
        double step_uv = clamp_double(
            delta_uv,
            -max_fall_step_uv,
            max_rise_step_uv);

        state->corrected_uv += step_uv;
    }

    return state->corrected_uv;
}

static int open_tcp_server(uint16_t port)
{
    int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK, 0);

    if (fd < 0) {
        perror("socket");
        return -1;
    }

    int enable = 1;
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR,
                   &enable, sizeof(enable)) < 0) {
        perror("setsockopt(SO_REUSEADDR)");
        close(fd);
        return -1;
    }

    struct sockaddr_in local;
    memset(&local, 0, sizeof(local));
    local.sin_family = AF_INET;
    local.sin_addr.s_addr = htonl(INADDR_ANY);
    local.sin_port = htons(port);

    if (bind(fd, (struct sockaddr *)&local, sizeof(local)) < 0) {
        perror("bind");
        close(fd);
        return -1;
    }

    if (listen(fd, TCP_MAX_CLIENTS) < 0) {
        perror("listen");
        close(fd);
        return -1;
    }

    return fd;
}

struct tcp_client {
    int fd;
    char rx[TCP_RX_BUFFER_SIZE];
    size_t used;
};

static void close_tcp_client(struct tcp_client *client)
{
    if (client->fd >= 0)
        close(client->fd);

    client->fd = -1;
    client->used = 0;
}

static void send_all_nonblocking(int fd, const char *buffer, size_t length)
{
    size_t sent = 0;

    while (sent < length) {
        ssize_t n = send(fd, buffer + sent, length - sent, MSG_NOSIGNAL);

        if (n > 0) {
            sent += (size_t)n;
            continue;
        }

        if (n < 0 && errno == EINTR)
            continue;

        if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK))
            break;

        break;
    }
}

static void handle_tcp_command(
    int fd,
    const char *command,
    double ch1_mdeg,
    double ch2_mdeg,
    double ch1_uv,
    double ch2_uv)
{
    char response[160];
    int length;

    if (strcmp(command, "#deg?") == 0) {
        length = snprintf(
            response,
            sizeof(response),
            "CH1=%.3f mdeg,CH2=%.3f mdeg\r\n",
            ch1_mdeg,
            ch2_mdeg
        );
    } else if (strcmp(command, "#vol?") == 0) {
        length = snprintf(
            response,
            sizeof(response),
            "CH1=%.6f mV,CH2=%.6f mV\r\n",
            ch1_uv / 1000.0,
            ch2_uv / 1000.0
        );
    } else if (strcmp(command, "quit") == 0 ||
               strcmp(command, "exit") == 0) {
        length = snprintf(response, sizeof(response), "BYE\r\n");
    } else if (command[0] == '\0') {
        return;
    } else {
        length = snprintf(response, sizeof(response), "ERR\r\n");
    }

    if (length > 0)
        send_all_nonblocking(fd, response, (size_t)length);
}

static void service_tcp_clients(
    int server_fd,
    struct tcp_client clients[TCP_MAX_CLIENTS],
    double ch1_mdeg,
    double ch2_mdeg,
    double ch1_uv,
    double ch2_uv)
{
    for (;;) {
        struct sockaddr_in peer;
        socklen_t peer_length = sizeof(peer);
        int client_fd = accept4(
            server_fd,
            (struct sockaddr *)&peer,
            &peer_length,
            SOCK_NONBLOCK | SOCK_CLOEXEC
        );

        if (client_fd < 0) {
            if (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR)
                perror("accept4");
            break;
        }

        int slot = -1;
        for (int i = 0; i < TCP_MAX_CLIENTS; ++i) {
            if (clients[i].fd < 0) {
                slot = i;
                break;
            }
        }

        if (slot < 0) {
            static const char busy[] = "BUSY\r\n";
            send_all_nonblocking(client_fd, busy, sizeof(busy) - 1U);
            close(client_fd);
            continue;
        }

        clients[slot].fd = client_fd;
        clients[slot].used = 0;

        static const char welcome[] =
            "CONNECTED: use #deg? or #vol?\r\n";
        send_all_nonblocking(client_fd, welcome, sizeof(welcome) - 1U);
    }

    for (int i = 0; i < TCP_MAX_CLIENTS; ++i) {
        struct tcp_client *client = &clients[i];

        if (client->fd < 0)
            continue;

        for (;;) {
            char temp[64];
            ssize_t n = recv(client->fd, temp, sizeof(temp), 0);

            if (n == 0) {
                close_tcp_client(client);
                break;
            }

            if (n < 0) {
                if (errno == EINTR)
                    continue;
                if (errno == EAGAIN || errno == EWOULDBLOCK)
                    break;
                close_tcp_client(client);
                break;
            }

            for (ssize_t j = 0; j < n; ++j) {
                unsigned char c = (unsigned char)temp[j];

                /* Ignore common Telnet negotiation bytes. */
                if (c == 0xFFU)
                    continue;

                if (c == '\r' || c == '\n') {
                    if (client->used > 0U) {
                        client->rx[client->used] = '\0';
                        handle_tcp_command(
                            client->fd,
                            client->rx,
                            ch1_mdeg,
                            ch2_mdeg,
                            ch1_uv,
                            ch2_uv
                        );

                        if (strcmp(client->rx, "quit") == 0 ||
                            strcmp(client->rx, "exit") == 0) {
                            close_tcp_client(client);
                            break;
                        }

                        client->used = 0;
                    }
                    continue;
                }

                if (client->used + 1U < sizeof(client->rx)) {
                    client->rx[client->used++] = (char)c;
                } else {
                    client->used = 0;
                    static const char error[] = "ERR command too long\r\n";
                    send_all_nonblocking(
                        client->fd,
                        error,
                        sizeof(error) - 1U
                    );
                }
            }

            if (client->fd < 0)
                break;
        }
    }
}

static void cleanup(void)
{
    stop_hardware_pwm();

    if (chip_select.fd >= 0) {
        deselect_cs();
        close(chip_select.fd);
    }

    if (drdy.fd >= 0)
        close(drdy.fd);

    if (spi_fd >= 0)
        close(spi_fd);
}

int main(int argc, char **argv)
{
    uint16_t tcp_port =
        argc > 1
        ? (uint16_t)strtoul(argv[1], NULL, 10)
        : 5005;

    int chip_fd = -1;
    int tcp_server_fd = -1;
    struct tcp_client tcp_clients[TCP_MAX_CLIENTS];

    for (int i = 0; i < TCP_MAX_CLIENTS; ++i) {
        tcp_clients[i].fd = -1;
        tcp_clients[i].used = 0;
    }

    signal(SIGINT, on_signal);
    signal(SIGTERM, on_signal);
    atexit(cleanup);

    chip_fd = open(
        GPIO_CHIP,
        O_RDONLY | O_CLOEXEC
    );

    if (chip_fd < 0) {
        perror(GPIO_CHIP);
        return EXIT_FAILURE;
    }

    const unsigned int cs_offsets[] = {
        GPIO_ADC_CS1,
        GPIO_ADC_CS2
    };

    const unsigned int drdy_offsets[] = {
        GPIO_ADC_DRDY
    };

    if (gpio_request(
            chip_fd,
            cs_offsets,
            2,
            GPIO_V2_LINE_FLAG_OUTPUT,
            0x3,
            "ads-cs",
            &chip_select) < 0 ||

        gpio_request(
            chip_fd,
            drdy_offsets,
            1,
            GPIO_V2_LINE_FLAG_INPUT,
            0,
            "ads-drdy",
            &drdy) < 0) {

        close(chip_fd);
        return EXIT_FAILURE;
    }

    close(chip_fd);

    spi_fd = open(
        SPI_DEVICE,
        O_RDWR | O_CLOEXEC
    );

    if (spi_fd < 0) {
        perror(SPI_DEVICE);
        return EXIT_FAILURE;
    }

    uint32_t mode = SPI_MODE_1 | SPI_NO_CS;
    uint8_t bits = 8;
    uint32_t speed = SPI_SPEED_HZ;

    if (ioctl(
            spi_fd,
            SPI_IOC_WR_MODE32,
            &mode) < 0 ||

        ioctl(
            spi_fd,
            SPI_IOC_WR_BITS_PER_WORD,
            &bits) < 0 ||

        ioctl(
            spi_fd,
            SPI_IOC_WR_MAX_SPEED_HZ,
            &speed) < 0) {

        perror("SPI configuration");
        return EXIT_FAILURE;
    }

    if (ads_init() < 0)
        return EXIT_FAILURE;

    tcp_server_fd = open_tcp_server(tcp_port);

    if (tcp_server_fd < 0) {
        fprintf(stderr, "TCP server startup failed on port %u\n", tcp_port);
        return EXIT_FAILURE;
    }

    fprintf(stderr,
            "TCP command server listening on port %u "
            "(up to %u clients)\n",
            tcp_port,
            TCP_MAX_CLIENTS);

    struct channel_state channels[2] = {0};

    unsigned int selected_channel = 0;
    uint64_t pwm_epoch = 0;
    uint64_t missed_cycles = 0;
    unsigned int warmup_cycles = 20U;
    struct guard_state guard[2] = {0};

    if (retry_ads_select_channel(selected_channel) < 0)
        return EXIT_FAILURE;

    if (start_hardware_pwm(&pwm_epoch) < 0)
        return EXIT_FAILURE;

    uint64_t last_rising_edge = 0;
    uint64_t last_report = pwm_epoch;

    fprintf(stderr,
            "GPIO18/GPIO19 hardware PWM: 1 kHz complementary, "
            "ADC synchronized to GPIO18 edges\n");

    while (running) {
    int valid_high = 0;
    int valid_low = 0;

    struct channel_state *channel =
        &channels[selected_channel];

    uint64_t rising_edge = 0;
    uint64_t falling_edge = 0;

    if (wait_pwm_edge(0, 1, &rising_edge) < 0) {
        missed_cycles++;
        continue;
    }

    if (last_rising_edge != 0U) {
        uint64_t elapsed = rising_edge - last_rising_edge;
        uint64_t periods =
            (elapsed + PWM_PERIOD_US / 2U) / PWM_PERIOD_US;

        if (periods > 1U)
            missed_cycles += periods - 1U;
    }
    last_rising_edge = rising_edge;

    /*
     * HIGH phase
     */
    /*
     * MUX 책 챙 뮤셌モ 앪 ┚ヂ뼘뼙  챙탐 왗р 샕 ㅒ뼘Γ 온  책 챙탐흸챘짰 왗ⓥ궗흸챙  뮨 쒋꽓책 챦쩔쩍 챌짯흸챙큄 샖 쒋꽓책 챙탐 왗 궗징챌 씲궁ぢ뮨 쒋꽓책 챦쩔쩍 책 챙 ▣ 쒋꽓 책 챙탐 챘흹 졗 온시р ◈꼴 꿎 뮨  챙쨍챙 붌  챦쩔쩍
     * HIGH phase 책 챙탐흸챘짰 왗ⓥ궗흸챙  뮨 쒋꽓책 챦쩔쩍 책 챙탐 왗р 샕늘 온시 온  책 챙탐흸챘짰 ≥ 온시ヂㅒ뼙ぢ꼲ッ  챙 ▣ 쒋꽓책 챦쩔쩍 책 챙짭챘 걘 온시 온  챦쩔쩍창 샕Ｃр 샕늘┑꿎 ┚р 걘 쒋꽓챦쩔쩍챘쨘짙챘쩌  .
     */
    sleep_until_us(
        rising_edge + EXTERNAL_SETTLING_US
    );

    if (pwm1_level() == 1 &&
        ads_restart_and_read(&channel->high_raw) == 0 &&
        pwm1_level() == 1) {
        valid_high = 1;
    }

    if (!valid_high) {
        missed_cycles++;
        continue;
    }

    /*
     * LOW phase
     */

    if (wait_pwm_edge(1, 0, &falling_edge) < 0) {
        missed_cycles++;
        continue;
    }

    sleep_until_us(
        falling_edge + EXTERNAL_SETTLING_US
    );

    if (pwm1_level() == 0 &&
        ads_restart_and_read(&channel->low_raw) == 0 &&
        pwm1_level() == 0) {
        valid_low = 1;
    }

    if (!valid_low)
        missed_cycles++;

    /* Select the next channel for the following PWM cycle. */
    selected_channel ^= 1U;

    if (retry_ads_select_channel(selected_channel) < 0)
        break;

    /*
     * HIGH책 챙 ▣ 쒋꽓 LOW챈쨋챙 걘 쒋꽓 챌짯흸챘짚쨈챘짬   ㎴ 온  책 챙탐 챘짼징챈쨔짼챙 ▣ 쒋꽓책 챦쩔쩍 책 챙탐 챙힋짖책쩍 봤 온 
     * 1챦쩔쩍횓쩔챙    책 챙탐 왗 궗짙챦쩔쩍챙짖 샖 쒋꽓챦쩔쩍챦쩔쩍챘 ≤  책 챙탐 왗р 샕늘 온시р 슿셌 쒋꽓책 챦쩔쩍 책 챙 뮤셌モ 붋ッヂ㎮꽓책 챙탐흸챘짰 졗 온시 온 .
     */
    if (warmup_cycles > 0U) {
        warmup_cycles--;
    } else if (valid_high && valid_low) {
        accumulate_channel(channel);
    }

    /*
     * 책 챙탐 왗р 샕  온시ヂ   쒋꽓챌 ™ 쇒 온시ヂ    챌짯흸챙큄힋챘 슿  온시 온  책 챙탐 왗р 샕늘㎶뮻올 온  챦쩔쩍챗쩐짢챘 붴궗챔짬짯챘째챙  ▣  챦쩔쩍
     * 1챦쩔쩍횓쩔챙    책 챙탐 챘짠짝챦쩔쩍챦쩔쩍 챦쩔쩍창 샕Ｃр 샕늘┑꿎 ┚ 온  챌 왗р 걘 쒋꽓 UDP 책 챙탐 왗р 샕늘 온시 온  챦쩔쩍챘쨍챙  ▣ 온시ヂ매뮼р 샕늘 온시 온  책타타챘째쨍챙짹쨋책 챙쨍챙 붌  챦쩔쩍 책 챙탐 챘 붴궗챦쩔쩍챦쩔쩍.
     */

        uint64_t now = monotonic_us();

        if (now - last_report < REPORT_INTERVAL_US)
            continue;

        if (channels[0].sample_count == 0 ||
            channels[1].sample_count == 0) {
            last_report = now;
            continue;
        }

        uint32_t ch1_count =
            channels[0].sample_count;

        uint32_t ch2_count =
            channels[1].sample_count;

        int64_t ch1_vdiff_avg =
            channels[0].vdiff_sum / ch1_count;

        int64_t ch2_vdiff_avg =
            channels[1].vdiff_sum / ch2_count;

        int32_t ch1_vdiff_uv =
            code_to_uv(ch1_vdiff_avg);

        int32_t ch2_vdiff_uv =
            code_to_uv(ch2_vdiff_avg);

        double dt =
            (double)(now - last_report) / 1000000.0;

        double elapsed_time_s =
            (double)(now - pwm_epoch) / 1000000.0;

        double ch1_guard_vdiff_uv = guard_update(
            &guard[0],
            elapsed_time_s,
            (double)ch1_vdiff_uv,
            dt,
            CH1_GUARD_MAX_FALL_UV_PER_S,
            CH1_GUARD_MAX_RISE_UV_PER_S
        );

        double ch2_guard_vdiff_uv = guard_update(
            &guard[1],
            elapsed_time_s,
            (double)ch2_vdiff_uv,
            dt,
            CH2_GUARD_MAX_FALL_UV_PER_S,
            CH2_GUARD_MAX_RISE_UV_PER_S
        );

        /*
         * Existing 5 s LPF now receives only the guarded VDIFF.
         * These are the final voltage values returned by #vol?.
         */
        double alpha = dt / (LPF_TAU_SECONDS + dt);

        guard[0].lpf_uv +=
            alpha * (ch1_guard_vdiff_uv - guard[0].lpf_uv);

        guard[1].lpf_uv +=
            alpha * (ch2_guard_vdiff_uv - guard[1].lpf_uv);

        /*
         * Existing calibration and offsets are applied after the guarded LPF.
         * These are the final angle values returned by #deg?.
         */
        double ch1_lpf_mdeg_offset =
            fit_angle_mdeg(
                guard[0].lpf_uv / SENSOR_UV_PER_MDEG
            ) + offset_ch1;

        double ch2_lpf_mdeg_offset =
            fit_angle_mdeg(
                guard[1].lpf_uv / SENSOR_UV_PER_MDEG
            ) + offset_ch2;

        if (tcp_server_fd >= 0) {
            service_tcp_clients(
                tcp_server_fd,
                tcp_clients,
                ch1_lpf_mdeg_offset,
                ch2_lpf_mdeg_offset,
                guard[0].lpf_uv,
                guard[1].lpf_uv
            );
        }

        missed_cycles = 0;

        reset_channel_average(&channels[0]);
        reset_channel_average(&channels[1]);

        last_report = now;
    }

    for (int i = 0; i < TCP_MAX_CLIENTS; ++i)
        close_tcp_client(&tcp_clients[i]);

    if (tcp_server_fd >= 0)
        close(tcp_server_fd);

    return EXIT_SUCCESS;
}
