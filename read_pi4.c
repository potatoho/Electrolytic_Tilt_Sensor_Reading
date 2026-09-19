#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/gpio.h>
#include <linux/spi/spidev.h>
#include <math.h>
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
#define EXTERNAL_SETTLING_US 100U
#define DRDY_TIMEOUT_US      100U
#define ADC_SAMPLE_PERIOD_US   25ULL
#define ADS_RESET_SETTLE_US   50U
#define PWM_EDGE_TIMEOUT_US 3000U
#define REPORT_INTERVAL_US   1000000ULL
#define LPF_TAU_SECONDS       0.0

#define PHASE_SAMPLE_COUNT       10U
#define PHASE_KEEP_COUNT          5U
#define OUTPUT_WINDOW_COUNT    1024U  /* storage capacity for one report interval */
#define OUTPUT_TRIM_EACH_SIDE    10U

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
#define ADS_CMD_STOP       0x0AU
#define ADS_CMD_RDATA      0x12U
#define ADS_CMD_RREG       0x20U
#define ADS_CMD_WREG       0x40U

#define ADS_REG_ID         0x00U
#define ADS_REG_STATUS0    0x01U
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
#define ADS_STATUS0_DRDY             (1U << 2)

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

    /* One entry = VDIFF made from robust HIGH/LOW representatives. */
    int64_t vdiff_window[OUTPUT_WINDOW_COUNT];
    uint32_t sample_count;
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

static uint64_t diag_edge_fail = 0;
static uint64_t diag_prelevel_fail = 0;
static uint64_t diag_start_fail = 0;
static uint64_t diag_drdy_fail = 0;
static uint64_t diag_rdata_fail = 0;
static uint64_t diag_postlevel_fail = 0;

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
    /* Guard CS1/CS2 switching as in the working Pi3 workaround. */
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

static int ads_reset_configure_channel(unsigned int channel)
{
    uint8_t mux = channel == 0U
        ? ADS_MODE4_MUX_AIN0_AINCOM
        : ADS_MODE4_MUX_AIN1_AINCOM;

    if (ads_command(ADS_CMD_RESET) < 0) {
        fprintf(stderr, "ADS RESET failed\n");
        return -1;
    }

    usleep(ADS_RESET_SETTLE_US);

    if (ads_write_reg(ADS_REG_MODE3, ADS_MODE3_STATUS_OFF) < 0 ||
        ads_write_reg(ADS_REG_MODE0, ADS_MODE0_40000SPS) < 0 ||
        ads_write_reg(ADS_REG_MODE1, ADS_MODE1_CONTINUOUS_DELAY_50US) < 0) {
        fprintf(stderr, "ADS CS1 configuration failed after RESET\n");
        return -1;
    }

    if (ads_write_reg(ADS_REG_MODE4, mux | ADS_MODE4_GAIN_1) < 0) {
        fprintf(stderr, "CH%u MODE4 write failed after RESET\n", channel + 1U);
        return -1;
    }

    return 0;
}

static int wait_drdy_status(uint32_t timeout_us)
{
    uint64_t deadline = monotonic_us() + timeout_us;

    while (running && monotonic_us() < deadline) {
        uint8_t status0 = 0;

        if (ads_read_reg(ADS_REG_STATUS0, &status0) < 0)
            return -1;

        /* STATUS0.DRDY = 1 means conversion data are ready. */
        if ((status0 & ADS_STATUS0_DRDY) != 0U)
            return 0;
    }

    return -1;
}

/*
 * Pi4 acquisition strategy:
 *
 * - The ADC channel is configured once for the whole 1-ms PWM cycle.
 * - HIGH: START at rising edge, then collect 10 conversions in the same
 *   500-us HIGH half-period.
 * - LOW: START at falling edge, then collect 10 conversions in the same
 *   500-us LOW half-period.
 * - Only after the LOW block is complete do we RESET the ADC and configure
 *   MODE4 for the next channel.  This avoids the observed CS2-after-RDATA
 *   problem while preserving one VDIFF result per PWM cycle.
 *
 * Channels alternate every PWM period, so the design target is
 * Target is 500 VDIFF results/s per channel; each 1-s report uses however many valid results were actually collected.
 */

struct robust_candidate {
    int64_t value;
    uint64_t distance2;
};

static int compare_i64(const void *a, const void *b)
{
    int64_t va = *(const int64_t *)a;
    int64_t vb = *(const int64_t *)b;
    return (va > vb) - (va < vb);
}

static int compare_robust_candidate(const void *a, const void *b)
{
    const struct robust_candidate *ca = a;
    const struct robust_candidate *cb = b;

    if (ca->distance2 < cb->distance2)
        return -1;
    if (ca->distance2 > cb->distance2)
        return 1;
    return (ca->value > cb->value) - (ca->value < cb->value);
}

static uint64_t abs_i64_to_u64(int64_t value)
{
    return value < 0 ? (uint64_t)(-value) : (uint64_t)value;
}

/*
 * Robust mean:
 * 1) find the median of all input values,
 * 2) keep the values nearest to that median,
 * 3) average only the kept values.
 *
 * For an even input count, median2 = 2 * median is represented exactly as
 * sorted[N/2-1] + sorted[N/2].  Distances are therefore compared without
 * floating-point arithmetic.
 */
static int64_t median_nearest_mean(
    const int64_t *values,
    size_t count,
    size_t keep_count)
{
    int64_t sorted[OUTPUT_WINDOW_COUNT];
    struct robust_candidate candidates[OUTPUT_WINDOW_COUNT];

    if (count == 0U || keep_count == 0U ||
        keep_count > count || count > OUTPUT_WINDOW_COUNT)
        return 0;

    memcpy(sorted, values, count * sizeof(sorted[0]));
    qsort(sorted, count, sizeof(sorted[0]), compare_i64);

    int64_t median2;
    if ((count & 1U) != 0U) {
        median2 = 2 * sorted[count / 2U];
    } else {
        median2 = sorted[count / 2U - 1U] + sorted[count / 2U];
    }

    for (size_t i = 0; i < count; ++i) {
        candidates[i].value = values[i];
        candidates[i].distance2 =
            abs_i64_to_u64(2 * values[i] - median2);
    }

    qsort(candidates, count, sizeof(candidates[0]),
          compare_robust_candidate);

    int64_t sum = 0;
    for (size_t i = 0; i < keep_count; ++i)
        sum += candidates[i].value;

    return sum / (int64_t)keep_count;
}

/*
 * Second-stage report filter:
 * sort all VDIFF values collected during the last report interval,
 * discard the lowest 10 and highest 10, then average the remainder.
 * If <=20 values were collected, use all available values rather than
 * producing no result.
 */
static int64_t sigma3_mean_int64(
    const int64_t *samples,
    uint32_t count,
    uint32_t *accepted_out)
{
    if (accepted_out != NULL)
        *accepted_out = 0U;

    if (count == 0U)
        return 0;

    long double sum = 0.0L;
    for (uint32_t i = 0; i < count; ++i)
        sum += (long double)samples[i];

    long double mean = sum / (long double)count;

    long double sq_sum = 0.0L;
    for (uint32_t i = 0; i < count; ++i) {
        long double d = (long double)samples[i] - mean;
        sq_sum += d * d;
    }

    long double sigma = 0.0L;
    if (count > 1U)
        sigma = sqrtl(sq_sum / (long double)(count - 1U));

    /*
     * If sigma is zero, all samples are identical; use them all.
     */
    if (sigma == 0.0L) {
        if (accepted_out != NULL)
            *accepted_out = count;
        return (int64_t)llroundl(mean);
    }

    long double limit = 3.0L * sigma;
    long double filtered_sum = 0.0L;
    uint32_t accepted = 0U;

    for (uint32_t i = 0; i < count; ++i) {
        long double d = fabsl((long double)samples[i] - mean);
        if (d <= limit) {
            filtered_sum += (long double)samples[i];
            accepted++;
        }
    }

    /*
     * Safety fallback: this should not normally happen, but do not divide by zero.
     */
    if (accepted == 0U) {
        accepted = count;
        filtered_sum = sum;
    }

    if (accepted_out != NULL)
        *accepted_out = accepted;

    return (int64_t)llroundl(filtered_sum / (long double)accepted);
}

static int32_t phase_robust_mean(const int32_t samples[PHASE_SAMPLE_COUNT])
{
    int64_t values[PHASE_SAMPLE_COUNT];

    for (size_t i = 0; i < PHASE_SAMPLE_COUNT; ++i)
        values[i] = samples[i];

    return (int32_t)median_nearest_mean(
        values,
        PHASE_SAMPLE_COUNT,
        PHASE_KEEP_COUNT
    );
}

/*
 * Start/restart continuous conversion immediately after the PWM edge.
 * During EXTERNAL_SETTLING_US the ADC keeps converting.  After settling,
 * read 10 results from the same excitation phase, paced at 25 us. STATUS0 is
 * not polled inside the sample loop so the 10 reads fit within 500 us.
 */
static int ads_collect_phase_samples(
    int expected_pwm_level,
    int32_t *representative)
{
    uint64_t edge_us = 0;

    if (wait_pwm_edge(expected_pwm_level ? 0 : 1,
                      expected_pwm_level ? 1 : 0,
                      &edge_us) < 0) {
        diag_edge_fail++;
        return -1;
    }

    sleep_until_us(edge_us + EXTERNAL_SETTLING_US);

    if (pwm1_level() != expected_pwm_level) {
        diag_prelevel_fail++;
        return -1;
    }

    if (ads_command(ADS_CMD_START) < 0) {
        diag_start_fail++;
        return -1;
    }

    if (wait_drdy_status(DRDY_TIMEOUT_US) < 0) {
        diag_drdy_fail++;
        return -1;
    }

    if (ads_read_data(representative) < 0) {
        diag_rdata_fail++;
        return -1;
    }

    /*
     * Do not reject based on PWM level after RDATA.
     * The conversion was already started and completed in the intended phase.
     * Linux/SPI readout may finish after the excitation edge without invalidating
     * the conversion result that is already stored in the ADC data register.
     */
    return 0;
}

static int recover_and_configure_channel(unsigned int channel)
{
    for (unsigned int attempt = 1U; attempt <= 5U; ++attempt) {
        if (ads_reset_configure_channel(channel) == 0)
            return 0;

        if (attempt == 1U || attempt == 5U) {
            fprintf(stderr,
                    "CH%u RESET/MUX recovery failed (%u/5)\n",
                    channel + 1U, attempt);
        }
        usleep(100);
    }

    return -1;
}

static void accumulate_channel(
    struct channel_state *channel)
{
    if (channel->sample_count >= OUTPUT_WINDOW_COUNT)
        return;

    int64_t high = channel->high_raw;
    int64_t low = channel->low_raw;
    int64_t vdiff = (high - low) / 2;

    channel->high_sum += high;
    channel->low_sum += low;
    channel->vdiff_window[channel->sample_count] = vdiff;
    channel->sample_count++;
}

static void reset_channel_average(
    struct channel_state *channel)
{
    channel->high_sum = 0;
    channel->low_sum = 0;
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

/* Fifth-order calibration is intentionally disabled for this test. */
#if 0
static double fit_angle_mdeg(double t)
{
    return ((((-4.20529061e-17 * t
               - 7.57486695e-13) * t
              + 9.26577767e-9) * t
             - 1.15097020e-5) * t
            + 0.916180507) * t
           - 0.568154573;
}
#endif

static int open_udp(
    const char *address,
    uint16_t port,
    struct sockaddr_in *destination)
{
    int fd = socket(
        AF_INET,
        SOCK_DGRAM | SOCK_NONBLOCK,
        0
    );

    if (fd < 0)
        return -1;

    memset(destination, 0, sizeof(*destination));

    destination->sin_family = AF_INET;
    destination->sin_port = htons(port);

    if (inet_pton(
            AF_INET,
            address,
            &destination->sin_addr) != 1) {
        close(fd);
        return -1;
    }

    return fd;
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
    const char *udp_address =
        argc > 1 ? argv[1] : "192.168.1.100";

    uint16_t udp_port =
        argc > 2
        ? (uint16_t)strtoul(argv[2], NULL, 10)
        : 5005;

    int chip_fd = -1;
    int udp_fd = -1;

    struct sockaddr_in udp_destination;

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

    udp_fd = open_udp(
        udp_address,
        udp_port,
        &udp_destination
    );

    if (udp_fd < 0) {
        fprintf(
            stderr,
            "UDP disabled: invalid destination or socket error\n"
        );
    }

    struct channel_state channels[2] = {0};

    unsigned int selected_channel = 0;
    uint64_t pwm_epoch = 0;
    uint64_t missed_cycles = 0;
    unsigned int warmup_cycles = 20U;
    double ch1_vdiff_lpf_uv = 0.0;
    double ch2_vdiff_lpf_uv = 0.0;
    double board_temp_lpf_mC = -1.0;
    int temp_lpf_initialized = 0;

    if (start_hardware_pwm(&pwm_epoch) < 0)
        return EXIT_FAILURE;

    uint64_t last_report = pwm_epoch;

    fprintf(stderr,
            "GPIO18/GPIO19 hardware PWM: 1 kHz complementary, "
            "ADC synchronized to GPIO18 edges\n");

    puts(
        "time_s,Temp_mC,"
        "CH1_VDIFF_uV,CH1_RAW_mdeg,CH1_kept,CH1_total,"
        "CH2_VDIFF_uV,CH2_RAW_mdeg,CH2_kept,CH2_total"
    );

    while (running) {
        int valid_high = 0;
        int valid_low = 0;

        struct channel_state *channel =
            &channels[selected_channel];

        /* HIGH: one conversion in the HIGH phase. */
        if (ads_collect_phase_samples(1, &channel->high_raw) == 0)
            valid_high = 1;

        if (!valid_high) {
            missed_cycles++;
            if (recover_and_configure_channel(selected_channel) < 0)
                break;
            goto report_check;
        }

        /* LOW: one conversion in the LOW phase. */
        if (ads_collect_phase_samples(0, &channel->low_raw) == 0)
            valid_low = 1;

        if (!valid_low) {
            missed_cycles++;
            if (recover_and_configure_channel(selected_channel) < 0)
                break;
            goto report_check;
        }

        if (warmup_cycles > 0U) {
            warmup_cycles--;
        } else {
            accumulate_channel(channel);
        }

        /*
         * RDATA has already occurred on CS1. Recover CS2 with RESET, then
         * configure the next channel before its next rising edge.
         */
        {
            unsigned int next_channel = selected_channel ^ 1U;
            if (recover_and_configure_channel(next_channel) < 0)
                break;
            selected_channel = next_channel;
        }

report_check:
        {
            uint64_t now = monotonic_us();
            if (now - last_report < REPORT_INTERVAL_US)
                continue;

            uint32_t ch1_count = channels[0].sample_count;
            uint32_t ch2_count = channels[1].sample_count;

            fprintf(stderr,
                    "[1s] CH1=%u CH2=%u missed=%llu "
                    "fail(e/p/s/d/r)=%llu/%llu/%llu/%llu/%llu\n",
                    ch1_count,
                    ch2_count,
                    (unsigned long long)missed_cycles,
                    (unsigned long long)diag_edge_fail,
                    (unsigned long long)diag_prelevel_fail,
                    (unsigned long long)diag_start_fail,
                    (unsigned long long)diag_drdy_fail,
                    (unsigned long long)diag_rdata_fail);

            /* Need at least one valid VDIFF from both channels for a CSV row. */
            if (ch1_count == 0U || ch2_count == 0U) {
                reset_channel_average(&channels[0]);
                reset_channel_average(&channels[1]);
                missed_cycles = 0;
                diag_edge_fail = 0;
                diag_prelevel_fail = 0;
                diag_start_fail = 0;
                diag_drdy_fail = 0;
                diag_rdata_fail = 0;
                diag_postlevel_fail = 0;
                last_report = now;
                continue;
            }

            /*
             * Second robust stage: compute mean and sample sigma over the
             * 1-second VDIFF window, reject samples outside mean +/- 3 sigma,
             * then average the retained samples.
             */
            uint32_t ch1_sigma_accepted = 0U;
            uint32_t ch2_sigma_accepted = 0U;

            int64_t ch1_vdiff_final = sigma3_mean_int64(
                channels[0].vdiff_window,
                ch1_count,
                &ch1_sigma_accepted
            );

            int64_t ch2_vdiff_final = sigma3_mean_int64(
                channels[1].vdiff_window,
                ch2_count,
                &ch2_sigma_accepted
            );

            int32_t ch1_vdiff_uv = code_to_uv(ch1_vdiff_final);
            int32_t ch2_vdiff_uv = code_to_uv(ch2_vdiff_final);

            /* raw mdeg after single HIGH/LOW sampling and 1-s 3-sigma filtering. */
            double ch1_angle_mdeg =
                ch1_vdiff_uv / SENSOR_UV_PER_MDEG;
            double ch2_angle_mdeg =
                ch2_vdiff_uv / SENSOR_UV_PER_MDEG;

            double dt =
                (double)(now - last_report) / 1000000.0;

            /* LPF disabled (tau = 0): output follows robust raw value. */
            ch1_vdiff_lpf_uv = (double)ch1_vdiff_uv;
            ch2_vdiff_lpf_uv = (double)ch2_vdiff_uv;

            double ch1_lpf_input_mdeg = ch1_angle_mdeg;
            double ch2_lpf_input_mdeg = ch2_angle_mdeg;

            /* Fifth-order calibration temporarily disabled. */
            double ch1_lpf_mdeg = ch1_lpf_input_mdeg;
            double ch2_lpf_mdeg = ch2_lpf_input_mdeg;

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
                } else if (LPF_TAU_SECONDS <= 0.0) {
                    board_temp_lpf_mC = (double)board_temp_mC;
                } else {
                    double alpha = dt / (LPF_TAU_SECONDS + dt);
                    board_temp_lpf_mC +=
                        alpha *
                        ((double)board_temp_mC - board_temp_lpf_mC);
                }
            }

            char console_message[256];

            int console_length = snprintf(
                console_message,
                sizeof(console_message),
                "%.3f,%d,"
                "%ld,%.3f,%u,%u,"
                "%ld,%.3f,%u,%u\n",
                elapsed_time_s,
                board_temp_mC,
                (long)ch1_vdiff_uv,
                ch1_angle_mdeg,
                ch1_sigma_accepted,
                ch1_count,
                (long)ch2_vdiff_uv,
                ch2_angle_mdeg,
                ch2_sigma_accepted,
                ch2_count
            );

            (void)console_length;
            fputs(console_message, stdout);
            fflush(stdout);

            char compact_message[128];

            int compact_length = snprintf(
                compact_message,
                sizeof(compact_message),
                "%.1f,%.3f,%.1f,%.3f\n",
                ch1_vdiff_lpf_uv,
                ch1_lpf_mdeg_offset,
                ch2_vdiff_lpf_uv,
                ch2_lpf_mdeg_offset
            );

            if (udp_fd >= 0 && compact_length > 0) {
                (void)sendto(
                    udp_fd,
                    compact_message,
                    (size_t)compact_length,
                    0,
                    (struct sockaddr *)&udp_destination,
                    sizeof(udp_destination)
                );
            }

            fprintf(stderr,
                    "[3sigma] CH1=%u/%u CH2=%u/%u\n",
                    ch1_sigma_accepted,
                    ch1_count,
                    ch2_sigma_accepted,
                    ch2_count);

            missed_cycles = 0;
            reset_channel_average(&channels[0]);
            reset_channel_average(&channels[1]);
            last_report = now;
        }
    }

    if (udp_fd >= 0)
        close(udp_fd);

    return EXIT_SUCCESS;
}
