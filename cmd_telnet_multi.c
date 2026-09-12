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
#define SPI_SPEED_HZ       8000000U

#define PWM_PERIOD_US       1000ULL
#define HALF_PERIOD_US       500ULL
#define EXTERNAL_SETTLING_US 200U
#define DRDY_TIMEOUT_US      250U
#define PWM_EDGE_TIMEOUT_US 3000U
#define REPORT_INTERVAL_US   1000000ULL
#define LPF_TAU_SECONDS       2.0
#define REPORT_SAMPLE_MAX      1024U
#define REPORT_MEDIAN_WINDOW      3U
#define OUTLIER_MIN_THRESHOLD_COUNTS 2000LL
#define OUTLIER_MAD_MULTIPLIER       6LL
#define OUTLIER_MIN_ACCEPTED_PAIRS     8U
#define REPORT_MIN_VALID_PAIRS        20U
#define ADS_RESET_SETTLE_US          200U

/* Per-channel electrical-spike detector, evaluated once per 1-s report.
 * D  = HIGH - LOW
 * CM = (HIGH + LOW) / 2
 * Same detector and thresholds are applied independently to CH1 and CH2.
 */
#define SPIKE_D_MIN_COUNTS              7000LL
#define SPIKE_CM_MIN_COUNTS             2000LL
#define SPIKE_CM_D_RATIO_NUM               8LL  /* 0.08 = 8 / 100 */
#define SPIKE_CM_D_RATIO_DEN             100LL
#define SPIKE_REJECT_MAX_REPORTS           15U
#define SPIKE_RELEASE_GOOD_REPORTS            2U
#define SPIKE_RELEASE_GUARD_REPORTS           2U
#define SPIKE_FAULT_RECOVERY_REPORTS         8U

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

    /* Per-report paired HIGH/LOW history for robust median/MAD filtering. */
    int32_t high_samples[REPORT_SAMPLE_MAX];
    int32_t low_samples[REPORT_SAMPLE_MAX];
    uint32_t stored_samples;
    uint32_t dropped_samples;
};

struct spike_filter_state {
    int initialized;
    int rejecting;
    int fault;

    int64_t previous_d;
    int64_t previous_cm;
    int64_t reference_cm;

    uint32_t reject_reports;
    uint32_t release_good_reports;
    uint32_t release_guard_reports;
    uint32_t recovery_good_reports;
};

struct spike_filter_result {
    int reject;
    int fault;
    int edge;
    int64_t d;
    int64_t cm;
    int64_t delta_d;
    int64_t delta_cm;
};

static int64_t abs_i64(int64_t value)
{
    return value < 0 ? -value : value;
}

/*
 * Common, per-channel electrical-spike discriminator.
 * No CH1/CH2 cross-comparison and no tilt-speed limit are used.
 */
static struct spike_filter_result update_spike_filter(
    struct spike_filter_state *state,
    int64_t high,
    int64_t low)
{
    struct spike_filter_result result = {0};

    int64_t d = high - low;
    int64_t cm = (high + low) / 2LL;
    result.d = d;
    result.cm = cm;

    if (!state->initialized) {
        state->initialized = 1;
        state->previous_d = d;
        state->previous_cm = cm;
        state->reference_cm = cm;
        return result;
    }

    int64_t delta_d = d - state->previous_d;
    int64_t delta_cm = cm - state->previous_cm;
    int64_t abs_delta_d = abs_i64(delta_d);
    int64_t abs_delta_cm = abs_i64(delta_cm);

    result.delta_d = delta_d;
    result.delta_cm = delta_cm;

    result.edge =
        abs_delta_d > SPIKE_D_MIN_COUNTS &&
        abs_delta_cm > SPIKE_CM_MIN_COUNTS &&
        abs_delta_cm * SPIKE_CM_D_RATIO_DEN >
            abs_delta_d * SPIKE_CM_D_RATIO_NUM;

    if (state->fault) {
        int electrically_stable =
            !result.edge &&
            abs_delta_cm <= SPIKE_CM_MIN_COUNTS;

        if (electrically_stable) {
            state->recovery_good_reports++;
            if (state->recovery_good_reports >=
                SPIKE_FAULT_RECOVERY_REPORTS) {
                state->fault = 0;
                state->rejecting = 0;
                state->reject_reports = 0U;
                state->release_good_reports = 0U;
                state->release_guard_reports = 0U;
                state->recovery_good_reports = 0U;
                state->reference_cm = cm;
            }
        } else {
            state->recovery_good_reports = 0U;
        }

        result.fault = state->fault;
        result.reject = state->fault;
    } else if (state->rejecting) {
        state->reject_reports++;

        int release_candidate =
            !result.edge &&
            abs_i64(cm - state->reference_cm) <= SPIKE_CM_MIN_COUNTS;

        if (state->release_guard_reports > 0U) {
            if (result.edge) {
                state->release_guard_reports = 0U;
                state->release_good_reports = 0U;
                result.reject = 1;
            } else {
                state->release_guard_reports--;
                result.reject = 1;

                if (state->release_guard_reports == 0U) {
                    state->rejecting = 0;
                    state->reject_reports = 0U;
                    state->release_good_reports = 0U;
                    state->reference_cm = cm;
                }
            }
        } else if (release_candidate) {
            state->release_good_reports++;
            result.reject = 1;

            if (state->release_good_reports >=
                SPIKE_RELEASE_GOOD_REPORTS) {
                state->release_good_reports = 0U;
                state->release_guard_reports =
                    SPIKE_RELEASE_GUARD_REPORTS;
            }
        } else {
            state->release_good_reports = 0U;
            state->release_guard_reports = 0U;

            if (state->reject_reports >= SPIKE_REJECT_MAX_REPORTS) {
                state->fault = 1;
                state->recovery_good_reports = 0U;
                result.reject = 1;
                result.fault = 1;
            } else {
                result.reject = 1;
            }
        }
    } else if (result.edge) {
        state->rejecting = 1;
        state->reject_reports = 1U;
        state->release_good_reports = 0U;
        state->release_guard_reports = 0U;
        state->reference_cm = state->previous_cm;
        result.reject = 1;
    }

    state->previous_d = d;
    state->previous_cm = cm;
    result.fault = state->fault;

    return result;
}

static volatile sig_atomic_t running = 1;

static int spi_fd = -1;
static struct gpio_group chip_select = {-1, 0};
static struct gpio_group drdy = {-1, 0};
static volatile uint32_t *gpio_regs;
static volatile uint32_t *pwm_regs;
static volatile uint32_t *clk_regs;
static uint32_t saved_gpfsel1;
static int pwm_gpio_configured;

/* ADC/SPI recovery diagnostics. Single-threaded on Pi4, so atomics are not required. */
static uint64_t ads_start_failures = 0;
static uint64_t drdy_timeouts = 0;
static uint64_t rdata_failures = 0;
static uint64_t ads_recovery_attempts = 0;
static uint64_t ads_recovery_failures = 0;

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
    /* Force both CS lines inactive before changing devices and provide a
     * small setup/hold margin around each transaction.  This protects against
     * rare CS1/CS2 switching failures without changing the PWM excitation.
     */
    deselect_cs();
    usleep(2);

    if (select_cs(cs) < 0)
        return -1;

    usleep(1);
    int rc = spi_transfer(tx, rx, len);
    usleep(1);
    deselect_cs();
    usleep(2);

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

static int ads_recover_channel(unsigned int channel)
{
    uint8_t mux = channel == 0U
        ? ADS_MODE4_MUX_AIN0_AINCOM
        : ADS_MODE4_MUX_AIN1_AINCOM;

    ads_recovery_attempts++;
    deselect_cs();
    usleep(10);

    if (ads_command(ADS_CMD_RESET) < 0) {
        ads_recovery_failures++;
        return -1;
    }

    usleep(ADS_RESET_SETTLE_US);

    if (ads_write_reg(ADS_REG_MODE3, ADS_MODE3_STATUS_OFF) < 0 ||
        ads_write_reg(ADS_REG_MODE0, ADS_MODE0_40000SPS) < 0 ||
        ads_write_reg(ADS_REG_MODE1, ADS_MODE1_CONTINUOUS_DELAY_50US) < 0 ||
        ads_write_reg(ADS_REG_MODE4, mux | ADS_MODE4_GAIN_1) < 0) {
        ads_recovery_failures++;
        return -1;
    }

    return 0;
}

static int ads_restart_and_read(unsigned int channel, int32_t *raw)
{
    if (ads_command(ADS_CMD_START) < 0) {
        ads_start_failures++;
        (void)ads_recover_channel(channel);
        return -1;
    }

    if (wait_drdy_falling_edge(DRDY_TIMEOUT_US) < 0) {
        drdy_timeouts++;
        (void)ads_recover_channel(channel);
        return -1;
    }

    if (ads_read_data(raw) < 0) {
        rdata_failures++;
        (void)ads_recover_channel(channel);
        return -1;
    }

    return 0;
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

    /* Keep each valid HIGH/LOW pair for report-level robust filtering. */
    if (channel->stored_samples < REPORT_SAMPLE_MAX) {
        channel->high_samples[channel->stored_samples] = channel->high_raw;
        channel->low_samples[channel->stored_samples] = channel->low_raw;
        channel->stored_samples++;
    } else {
        channel->dropped_samples++;
    }
}

static void reset_channel_average(
    struct channel_state *channel)
{
    channel->high_sum = 0;
    channel->low_sum = 0;
    channel->vcm_sum = 0;
    channel->vdiff_sum = 0;
    channel->sample_count = 0;
    channel->stored_samples = 0;
    channel->dropped_samples = 0;
}

static int compare_int32(const void *a, const void *b)
{
    int32_t aa = *(const int32_t *)a;
    int32_t bb = *(const int32_t *)b;
    return (aa > bb) - (aa < bb);
}

static int32_t median_int32(const int32_t *samples, uint32_t count)
{
    if (count == 0U)
        return 0;
    if (count > REPORT_SAMPLE_MAX)
        count = REPORT_SAMPLE_MAX;

    int32_t work[REPORT_SAMPLE_MAX];
    memcpy(work, samples, count * sizeof(work[0]));
    qsort(work, count, sizeof(work[0]), compare_int32);

    if ((count & 1U) != 0U)
        return work[count / 2U];

    return (int32_t)(((int64_t)work[count / 2U - 1U] +
                      (int64_t)work[count / 2U]) / 2LL);
}

static int compare_int64(const void *a, const void *b)
{
    int64_t aa = *(const int64_t *)a;
    int64_t bb = *(const int64_t *)b;
    return (aa > bb) - (aa < bb);
}

static int64_t median_int64(const int64_t *samples, uint32_t count)
{
    if (count == 0U)
        return 0;
    if (count > REPORT_SAMPLE_MAX)
        count = REPORT_SAMPLE_MAX;

    int64_t work[REPORT_SAMPLE_MAX];
    memcpy(work, samples, count * sizeof(work[0]));
    qsort(work, count, sizeof(work[0]), compare_int64);

    if ((count & 1U) != 0U)
        return work[count / 2U];

    return (work[count / 2U - 1U] + work[count / 2U]) / 2LL;
}

static int64_t mad_int32(
    const int32_t *samples,
    uint32_t count,
    int32_t median)
{
    if (count == 0U)
        return 0;
    if (count > REPORT_SAMPLE_MAX)
        count = REPORT_SAMPLE_MAX;

    int32_t deviations[REPORT_SAMPLE_MAX];
    for (uint32_t i = 0; i < count; ++i) {
        int64_t d = (int64_t)samples[i] - median;
        if (d < 0) d = -d;
        if (d > INT32_MAX) d = INT32_MAX;
        deviations[i] = (int32_t)d;
    }

    return (int64_t)median_int32(deviations, count);
}

static int64_t adaptive_outlier_threshold(int64_t mad)
{
    int64_t threshold = OUTLIER_MAD_MULTIPLIER * mad;
    if (threshold < OUTLIER_MIN_THRESHOLD_COUNTS)
        threshold = OUTLIER_MIN_THRESHOLD_COUNTS;
    return threshold;
}

struct robust_pair_average {
    int64_t high_mean;
    int64_t low_mean;
    uint32_t accepted;
    uint32_t rejected;
    int fallback_used;
};

static struct robust_pair_average robust_pair_mean(
    const int32_t *high_samples,
    const int32_t *low_samples,
    uint32_t count,
    int32_t high_median,
    int32_t low_median,
    int64_t high_threshold,
    int64_t low_threshold)
{
    struct robust_pair_average r = {0};
    if (count == 0U)
        return r;
    if (count > REPORT_SAMPLE_MAX)
        count = REPORT_SAMPLE_MAX;

    int64_t hs = 0;
    int64_t ls = 0;

    for (uint32_t i = 0; i < count; ++i) {
        int64_t dh = (int64_t)high_samples[i] - high_median;
        int64_t dl = (int64_t)low_samples[i] - low_median;
        if (dh < 0) dh = -dh;
        if (dl < 0) dl = -dl;

        if (dh > high_threshold || dl > low_threshold) {
            r.rejected++;
            continue;
        }

        hs += high_samples[i];
        ls += low_samples[i];
        r.accepted++;
    }

    if (r.accepted < OUTLIER_MIN_ACCEPTED_PAIRS ||
        r.accepted * 2U < count) {
        hs = 0;
        ls = 0;
        for (uint32_t i = 0; i < count; ++i) {
            hs += high_samples[i];
            ls += low_samples[i];
        }
        r.accepted = count;
        r.fallback_used = 1;
    }

    if (r.accepted > 0U) {
        r.high_mean = hs / (int64_t)r.accepted;
        r.low_mean = ls / (int64_t)r.accepted;
    }
    return r;
}

static int64_t robust_pair_vdiff_median(
    const int32_t *high_samples,
    const int32_t *low_samples,
    uint32_t count,
    int32_t high_median,
    int32_t low_median,
    int64_t high_threshold,
    int64_t low_threshold,
    uint32_t *accepted_out)
{
    if (count > REPORT_SAMPLE_MAX)
        count = REPORT_SAMPLE_MAX;

    int64_t vdiff_samples[REPORT_SAMPLE_MAX];
    uint32_t accepted = 0U;

    for (uint32_t i = 0; i < count; ++i) {
        int64_t dh = (int64_t)high_samples[i] - high_median;
        int64_t dl = (int64_t)low_samples[i] - low_median;
        if (dh < 0) dh = -dh;
        if (dl < 0) dl = -dl;
        if (dh > high_threshold || dl > low_threshold)
            continue;

        vdiff_samples[accepted++] =
            ((int64_t)high_samples[i] - (int64_t)low_samples[i]) / 2LL;
    }

    if (accepted_out != NULL)
        *accepted_out = accepted;
    if (accepted == 0U)
        return 0;
    return median_int64(vdiff_samples, accepted);
}

/*
 * Stage 2 median:
 * median of the most recent REPORT_MEDIAN_WINDOW report medians.
 * With one/two reports available at startup, use the median of what exists.
 */
static int32_t push_report_median(
    int32_t history[REPORT_MEDIAN_WINDOW],
    uint32_t *count,
    uint32_t *write_index,
    int32_t value)
{
    history[*write_index] = value;
    *write_index = (*write_index + 1U) % REPORT_MEDIAN_WINDOW;

    if (*count < REPORT_MEDIAN_WINDOW)
        (*count)++;

    int32_t work[REPORT_MEDIAN_WINDOW];
    for (uint32_t i = 0; i < *count; ++i)
        work[i] = history[i];

    for (uint32_t i = 1; i < *count; ++i) {
        int32_t key = work[i];
        uint32_t j = i;
        while (j > 0U && work[j - 1U] > key) {
            work[j] = work[j - 1U];
            --j;
        }
        work[j] = key;
    }

    if ((*count & 1U) != 0U)
        return work[*count / 2U];

    return (int32_t)(((int64_t)work[*count / 2U - 1U] +
                      (int64_t)work[*count / 2U]) / 2LL);
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
    double ch1_vdiff_lpf_uv = 0.0;
    double ch2_vdiff_lpf_uv = 0.0;
    double board_temp_lpf_mC = -1.0;
    int ch1_lpf_initialized = 0;
    int ch2_lpf_initialized = 0;
    int temp_lpf_initialized = 0;
    struct spike_filter_state spike_state[2] = {{0}, {0}};

    /*
     * Two-stage median filter state:
     *   1) median of all paired VDIFF samples inside each report
     *   2) median of the most recent 3 report medians
     * The resulting value is the input to the existing LPF.
     */
    int32_t ch1_report_median_history[REPORT_MEDIAN_WINDOW] = {0};
    int32_t ch2_report_median_history[REPORT_MEDIAN_WINDOW] = {0};
    uint32_t ch1_report_median_count = 0U;
    uint32_t ch2_report_median_count = 0U;
    uint32_t ch1_report_median_index = 0U;
    uint32_t ch2_report_median_index = 0U;

    if (retry_ads_select_channel(selected_channel) < 0)
        return EXIT_FAILURE;

    if (start_hardware_pwm(&pwm_epoch) < 0)
        return EXIT_FAILURE;

    uint64_t last_rising_edge = 0;
    uint64_t last_report = pwm_epoch;

    fprintf(stderr,
            "GPIO18/GPIO19 hardware PWM: 1 kHz complementary, "
            "ADC synchronized to GPIO18 edges\n");

    puts(
        "time,Temp_raw_mC,Temp_LPF_mC,"
        "CH1_HIGH_raw,CH1_LOW_raw,CH1_VDIFF_raw_uV,"
        "CH1_VDIFF_mdeg,CH1_LPF_fitted_mdeg,CH1_LPF_fitted_mdeg_offset,"
        "CH2_HIGH_raw,CH2_LOW_raw,CH2_VDIFF_raw_uV,"
        "CH2_VDIFF_mdeg,CH2_LPF_fitted_mdeg,CH2_LPF_fitted_mdeg_offset"
    );

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
     * MUX å ì‹¼ë”…ë»»å ìŽ„ì‘¬ä»¥ï¿½ å ìŽŒë®„è€Œìˆ‹ì˜™å ï¿½ ç­Œìš‘ì˜™å ìŽ„í€¡ç”±ê¹ì˜™å ï¿½ å ì™ì˜™ å ìŽˆëœ†ï¿½ì•²ì²‹å ì¸ì—å ï¿½
     * HIGH phase å ìŽŒë®„è€Œìˆ‹ì˜™å ï¿½ å ìŽ„ì‘´ï¿½ï¿½ å ìŽŒë®‡ï¿½ë¤»ê²«å ì™ì˜™å ï¿½ å ì¬ë‰ï¿½ï¿½ ï¿½â‘£ì‘´æ²…ì‰ì˜™ï¿½ëº£ë¼„.
     */
    sleep_until_us(
        rising_edge + EXTERNAL_SETTLING_US
    );

    if (pwm1_level() == 1 &&
        ads_restart_and_read(selected_channel, &channel->high_raw) == 0 &&
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
        ads_restart_and_read(selected_channel, &channel->low_raw) == 0 &&
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
     * HIGHå ì™ì˜™ LOWæ¶ì‰ì˜™ ç­Œë¤´ë«€ï§ï¿½ å ìŽˆë²¡æ¹²ì™ì˜™å ï¿½ å ìŽˆìŠ¢å½›ï¿½
     * 1ï¿½Î¿ì˜™ å ìŽ„í€£ï¿½ì¢‘ì˜™ï¿½ï¿½ë‡§ å ìŽ„ì‘´ï¿½ì‚¼ì˜™å ï¿½ å ì‹¼ë—«ë§™å ìŽŒë®†ï¿½ï¿½.
     */
    if (warmup_cycles > 0U) {
        warmup_cycles--;
    } else if (valid_high && valid_low) {
        accumulate_channel(channel);
    }

    /*
     * å ìŽ„ì‘¬ï¿½ë¯­ì˜™ç™’ï¿½ë®‰ ç­ŒìšŠë‚¯ï¿½ï¿½ å ìŽ„ì‘´çŒ¿ï¿½ ï¿½ê¾¨ë—€è«­ë°ì˜™å ï¿½
     * 1ï¿½Î¿ì˜™ å ìŽˆë§¦ï¿½ï¿½ ï¿½â‘£ì‘´æ²…ï¿½ ç„ì‰ì˜™ UDP å ìŽ„ì‘´ï¿½ï¿½ ï¿½ë¸ì˜™ï¿½ë¸Œì‘´ï¿½ï¿½ åŸŸë°¸ì±¶å ì¸ì—å ï¿½ å ìŽˆë—€ï¿½ï¿½.
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

        uint32_t ch1_stored = channels[0].stored_samples;
        uint32_t ch2_stored = channels[1].stored_samples;

        int32_t ch1_high_median =
            median_int32(channels[0].high_samples, ch1_stored);
        int32_t ch1_low_median =
            median_int32(channels[0].low_samples, ch1_stored);
        int32_t ch2_high_median =
            median_int32(channels[1].high_samples, ch2_stored);
        int32_t ch2_low_median =
            median_int32(channels[1].low_samples, ch2_stored);

        int64_t ch1_high_threshold = adaptive_outlier_threshold(
            mad_int32(channels[0].high_samples, ch1_stored, ch1_high_median));
        int64_t ch1_low_threshold = adaptive_outlier_threshold(
            mad_int32(channels[0].low_samples, ch1_stored, ch1_low_median));
        int64_t ch2_high_threshold = adaptive_outlier_threshold(
            mad_int32(channels[1].high_samples, ch2_stored, ch2_high_median));
        int64_t ch2_low_threshold = adaptive_outlier_threshold(
            mad_int32(channels[1].low_samples, ch2_stored, ch2_low_median));

        struct robust_pair_average ch1_robust = robust_pair_mean(
            channels[0].high_samples, channels[0].low_samples, ch1_stored,
            ch1_high_median, ch1_low_median,
            ch1_high_threshold, ch1_low_threshold);
        struct robust_pair_average ch2_robust = robust_pair_mean(
            channels[1].high_samples, channels[1].low_samples, ch2_stored,
            ch2_high_median, ch2_low_median,
            ch2_high_threshold, ch2_low_threshold);

        uint32_t ch1_median_accepted = 0U;
        uint32_t ch2_median_accepted = 0U;
        int64_t ch1_vdiff_sample_median = robust_pair_vdiff_median(
            channels[0].high_samples, channels[0].low_samples, ch1_stored,
            ch1_high_median, ch1_low_median,
            ch1_high_threshold, ch1_low_threshold,
            &ch1_median_accepted);
        int64_t ch2_vdiff_sample_median = robust_pair_vdiff_median(
            channels[1].high_samples, channels[1].low_samples, ch2_stored,
            ch2_high_median, ch2_low_median,
            ch2_high_threshold, ch2_low_threshold,
            &ch2_median_accepted);

        int64_t ch1_high_avg = ch1_robust.high_mean;
        int64_t ch1_low_avg = ch1_robust.low_mean;
        int64_t ch2_high_avg = ch2_robust.high_mean;
        int64_t ch2_low_avg = ch2_robust.low_mean;

        int32_t ch1_vdiff_uv = code_to_uv(ch1_vdiff_sample_median);
        int32_t ch2_vdiff_uv = code_to_uv(ch2_vdiff_sample_median);

        double ch1_angle_mdeg =
            ch1_vdiff_uv / SENSOR_UV_PER_MDEG;

        double ch2_angle_mdeg =
            ch2_vdiff_uv / SENSOR_UV_PER_MDEG;

        double dt =
            (double)(now - last_report) / 1000000.0;
        double alpha = dt / (LPF_TAU_SECONDS + dt);

        /*
         * Basic electrical-spike detector.  CH1 and CH2 use exactly the same
         * thresholds but independent state machines.  A rejected report is
         * NOT inserted into the 3-report median history, and the channel LPF
         * state is held at the last accepted value.
         */
        int ch1_report_valid =
            !ch1_robust.fallback_used &&
            ch1_robust.accepted >= REPORT_MIN_VALID_PAIRS &&
            ch1_median_accepted >= REPORT_MIN_VALID_PAIRS;
        int ch2_report_valid =
            !ch2_robust.fallback_used &&
            ch2_robust.accepted >= REPORT_MIN_VALID_PAIRS &&
            ch2_median_accepted >= REPORT_MIN_VALID_PAIRS;

        struct spike_filter_result ch1_spike = {
            .reject = spike_state[0].rejecting || spike_state[0].fault,
            .fault = spike_state[0].fault,
            .edge = 0
        };
        struct spike_filter_result ch2_spike = {
            .reject = spike_state[1].rejecting || spike_state[1].fault,
            .fault = spike_state[1].fault,
            .edge = 0
        };

        if (ch1_report_valid)
            ch1_spike = update_spike_filter(
                &spike_state[0], ch1_high_avg, ch1_low_avg);
        if (ch2_report_valid)
            ch2_spike = update_spike_filter(
                &spike_state[1], ch2_high_avg, ch2_low_avg);

        if (ch1_report_valid && !ch1_spike.reject && !ch1_spike.fault) {
            int32_t ch1_report_median_uv =
                push_report_median(
                    ch1_report_median_history,
                    &ch1_report_median_count,
                    &ch1_report_median_index,
                    ch1_vdiff_uv);

            if (!ch1_lpf_initialized) {
                ch1_vdiff_lpf_uv = (double)ch1_report_median_uv;
                ch1_lpf_initialized = 1;
            } else {
                ch1_vdiff_lpf_uv +=
                    alpha * ((double)ch1_report_median_uv - ch1_vdiff_lpf_uv);
            }
        }

        if (ch2_report_valid && !ch2_spike.reject && !ch2_spike.fault) {
            int32_t ch2_report_median_uv =
                push_report_median(
                    ch2_report_median_history,
                    &ch2_report_median_count,
                    &ch2_report_median_index,
                    ch2_vdiff_uv);

            if (!ch2_lpf_initialized) {
                ch2_vdiff_lpf_uv = (double)ch2_report_median_uv;
                ch2_lpf_initialized = 1;
            } else {
                ch2_vdiff_lpf_uv +=
                    alpha * ((double)ch2_report_median_uv - ch2_vdiff_lpf_uv);
            }
        }

        double ch1_lpf_input_mdeg =
            ch1_vdiff_lpf_uv / SENSOR_UV_PER_MDEG;

        double ch2_lpf_input_mdeg =
            ch2_vdiff_lpf_uv / SENSOR_UV_PER_MDEG;

        double ch1_lpf_mdeg =
            fit_angle_mdeg(ch1_lpf_input_mdeg);

        double ch2_lpf_mdeg =
            fit_angle_mdeg(ch2_lpf_input_mdeg);

        double ch1_lpf_mdeg_offset =
            ch1_lpf_mdeg + offset_ch1;

        double ch2_lpf_mdeg_offset =
            ch2_lpf_mdeg + offset_ch2;

        double elapsed_time_s =
            (double)(now - pwm_epoch) / 1000000.0;

        int board_temp_mC = read_board_temp_mC();

        if (board_temp_mC >= 0) {
            if (!temp_lpf_initialized) {
                board_temp_lpf_mC = (double)board_temp_mC;
                temp_lpf_initialized = 1;
            } else {
                double alpha = dt / (LPF_TAU_SECONDS + dt);

                board_temp_lpf_mC +=
                    alpha *
                    ((double)board_temp_mC - board_temp_lpf_mC);
            }
        }

        char console_message[448];

        int console_length = snprintf(
            console_message,
            sizeof(console_message),
            "%.3f,%d,%.1f,"
            "%lld,%lld,%ld,%.3f,%.3f,%.3f,"
            "%lld,%lld,%ld,%.3f,%.3f,%.3f\n",

            elapsed_time_s,
            board_temp_mC,
            temp_lpf_initialized ? board_temp_lpf_mC : -1.0,

            (long long)ch1_high_avg,
            (long long)ch1_low_avg,
            (long)ch1_vdiff_uv,
            ch1_angle_mdeg,
            ch1_lpf_mdeg,
            ch1_lpf_mdeg_offset,

            (long long)ch2_high_avg,
            (long long)ch2_low_avg,
            (long)ch2_vdiff_uv,
            ch2_angle_mdeg,
            ch2_lpf_mdeg,
            ch2_lpf_mdeg_offset
        );

        (void)console_length;


        if (tcp_server_fd >= 0) {
            service_tcp_clients(
                tcp_server_fd,
                tcp_clients,
                ch1_lpf_mdeg_offset,
                ch2_lpf_mdeg_offset,
                ch1_vdiff_lpf_uv,
                ch2_vdiff_lpf_uv
            );
        }

        fprintf(
            stderr,
            "averaged samples: CH1=%u, CH2=%u, skipped ADC cycles=%llu, "
            "spike CH1(edge=%d reject=%d fault=%d), "
            "CH2(edge=%d reject=%d fault=%d)\n",
            ch1_count,
            ch2_count,
            (unsigned long long)missed_cycles,
            ch1_spike.edge, ch1_spike.reject, ch1_spike.fault,
            ch2_spike.edge, ch2_spike.reject, ch2_spike.fault
        );

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
