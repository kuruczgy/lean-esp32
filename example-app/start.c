#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include <lean/lean.h>
#include <string.h>

#define REG(base, offs) *((volatile uint32_t *)((base) + (offs)))

#define UART_TXFIFO_WR_BYTE REG(0x60000000, 0x0)
#define UART_STATUS_REG REG(0x60000000, 0x1C)

#define USB_SERIAL_JTAG_EP1_REG REG(0x60043000, 0x0)
#define USB_SERIAL_JTAG_EP1_CONF_REG REG(0x60043000, 0x4)

#define GPIO_BASE 0x60004000
#define GPIO_IN_REG REG(GPIO_BASE, 0x3C)
#define GPIO_ENABLE_W1TS_REG REG(GPIO_BASE, 0x24)
#define GPIO_OUT_W1TS_REG REG(GPIO_BASE, 0x8)
#define GPIO_OUT_W1TC_REG REG(GPIO_BASE, 0xC)

#define RTC_BASE 0x60008000
#define RTC_CNTL_WDTCONFIG0_REG REG(RTC_BASE, 0x0090)
#define RTC_CNTL_WDTWPROTECT_REG REG(RTC_BASE, 0x00A8)
#define RTC_CNTL_SWD_CONF_REG REG(RTC_BASE, 0x00AC)
#define RTC_CNTL_SWD_WPROTECT_REG REG(RTC_BASE, 0x00B0)

#define TIMG0_BASE 0x6001F000
#define TIMG0_WDTCONFIG0_REG REG(TIMG0_BASE, 0x0048)
#define TIMG0_WDTPROTECT_REG REG(TIMG0_BASE, 0x0064)

static bool uart_is_busy() { return ((UART_STATUS_REG >> 16) & 0xF) > 8; }

static int uart_putc(char c, FILE *file) {
  (void)file;

  while (uart_is_busy())
    ;
  UART_TXFIFO_WR_BYTE = c;

  return c;
}

static int usb_putc(char c, FILE *file) {
  (void)file;

  while ((USB_SERIAL_JTAG_EP1_CONF_REG & (1 << 1)) == 0)
    ;
  USB_SERIAL_JTAG_EP1_REG = c;

  return c;
}

static int usb_flush(FILE *file) {
  USB_SERIAL_JTAG_EP1_CONF_REG |= 1;
  return 0;
}

static int dummy_getc(FILE *file) {
  (void)file;
  return '\0';
}

// Remove this to get output on the USB serial interface instead. Use something
// like `tio /dev/ttyACM0` to see the output from a real device.
#define UART_OUTPUT

#ifdef UART_OUTPUT
static FILE __stdio =
    FDEV_SETUP_STREAM(uart_putc, dummy_getc, NULL, _FDEV_SETUP_RW);
#else
static FILE __stdio =
    FDEV_SETUP_STREAM(usb_putc, dummy_getc, usb_flush, _FDEV_SETUP_RW);
#endif

FILE *const stdin = &__stdio;
__strong_reference(stdin, stdout);
__strong_reference(stdin, stderr);

void __attribute__((noreturn)) _exit(int status) {
  (void)status;

  // Semihosting exit
  __asm__(".option push;"
          ".option norvc;"
          "li a0, 0x18;"
          "li a1, 0;"
          "slli zero, zero, 0x1f;"
          "ebreak;"
          "srai zero, zero, 0x7;"
          ".option pop;"
          :
          :
          : "a0", "a1");

  while (1)
    ;
}

static void disable_wdt() {
  RTC_CNTL_WDTWPROTECT_REG = 0x50D83AA1;
  RTC_CNTL_WDTCONFIG0_REG &= ~(
      // RTC_CNTL_WDT_EN
      (1 << 31)
      // RTC_CNTL_WDT_FLASHBOOT_MOD_EN
      | (1 << 12));
  RTC_CNTL_WDTWPROTECT_REG = 0;

  RTC_CNTL_SWD_WPROTECT_REG = 0x8F1D312A;
  RTC_CNTL_SWD_CONF_REG |=
      // RTC_CNTL_SWD_AUTO_FEED_EN
      (1 << 31);
  RTC_CNTL_SWD_WPROTECT_REG = 0;

  TIMG0_WDTPROTECT_REG = 0x50D83AA1;
  TIMG0_WDTCONFIG0_REG &= ~(
      // TIMG_WDT_EN
      (1 << 31)
      // TIMG_WDT_FLASHBOOT_MOD_EN
      | (1 << 14));
  TIMG0_WDTPROTECT_REG = 0;
}

// Lean stubs
lean_object *initialize_Init(uint8_t builtin, lean_object *w) {
  return lean_io_result_mk_ok(lean_box(0));
}

int main(int argc, char **argv);

static inline void delay_4clk(uint32_t n) {
  for (size_t i = 0; i < n; ++i)
    __asm__("nop");
}

lean_object *c_delay_us(lean_object *t, lean_object *w) {
  delay_4clk(lean_unbox(t) * 5);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_object *c_flush(lean_object *w) {
  fflush(stdout);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_object *c_read_gpio(lean_object *_i, lean_object *w) {
  size_t i = lean_unbox(_i);
  uint32_t value = (GPIO_IN_REG >> i) & 1;
  return lean_io_result_mk_ok(lean_box(value));
}

static void enable_gpio(size_t i) {
  // GPIO_FUNCn_OUT_SEL_CFG_REG / GPIO_FUNCn_OUT_SEL
  REG(GPIO_BASE, 0x0554 + 4 * i) = 128;
  GPIO_ENABLE_W1TS_REG = 1 << i;
}

// for 20MHz clock
__attribute__((noinline)) void send_led_data(uint32_t data) {
  const size_t gpio = 10;
  for (size_t i = 0; i < 24; ++i) {
    const uint32_t bit = data & (1 << (23 - i)); // shift + and: 2 cycles
    GPIO_OUT_W1TS_REG = 1 << gpio;               // GPIO high: 1 cycle
    if (bit) {
      // if branch not taken: 1 cycles
      __asm__("nop; nop; nop; nop; nop;"
              "nop; nop; nop; nop; nop;"); // wait: 10 cycles
      GPIO_OUT_W1TC_REG = 1 << gpio;       // GPIO low: 1 cycle
      __asm__("nop;");                     // wait: 1 cycle
      // loop variable inc + jump taken: 4 cycles
    } else {
      // if branch taken: 3 cycles
      __asm__("nop; nop;");          // wait: 2 cycles
      GPIO_OUT_W1TC_REG = 1 << gpio; // GPIO low: 1 cycle
      __asm__("nop; nop; nop; nop; nop; nop; nop; nop; nop;"); // wait: 9 cycles
      // loop variable inc + jump not taken: 2 cycles
    }
  }
}

lean_object *c_set_led_state(lean_object *state, lean_object *w) {
  uint32_t data = lean_ctor_get_uint8(state, 0) << 16 |
                  lean_ctor_get_uint8(state, 1) << 8 |
                  lean_ctor_get_uint8(state, 2);
  send_led_data(data);
  return lean_io_result_mk_ok(lean_box(0));
}

extern char _bss_start, _bss_end;

void __attribute__((noreturn)) call_start_cpu0() {
  __asm__(".option push;"
          ".option norelax;"
          "la	sp, _stack_end;"
          "li tp, 0;"
          ".option pop;");

  memset(&_bss_start, 0, (&_bss_end - &_bss_start));

  disable_wdt();

  enable_gpio(10);

  main(0, 0);
  _exit(0);
}
