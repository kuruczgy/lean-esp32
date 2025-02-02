#![no_std]
#![no_main]

use esp_backtrace as _;
use esp_hal::{delay::Delay, main, rmt::Rmt, time, time::RateExtU32};
use esp_hal_smartled::{smartLedBuffer, SmartLedsAdapter};
use esp_println::println;
use log::info;
use smart_leds::{
    brightness, gamma,
    hsv::{hsv2rgb, Hsv},
    SmartLedsWrite,
};

#[main]
fn main() -> ! {
    // QEMU quirk
    // unsafe { (0x6002_3000 as *mut u32).write_volatile(1 << 30) };

    // let conf_val = unsafe { (0x6002_3000 as *mut u32).read_volatile() };
    // println!("systimer conf: {:#x}", conf_val);

    let config = esp_hal::Config::default().with_cpu_clock(esp_hal::clock::CpuClock::max());
    let peripherals = esp_hal::init(config);

    esp_println::logger::init_logger_from_env();

    // let xtal_freq_mhz = esp_hal::clock::Clocks::xtal_freq().to_MHz();
    // info!("xtal_freq_mhz: {}", xtal_freq_mhz);

    let led_pin = peripherals.GPIO10;

    let rmt = Rmt::new(peripherals.RMT, 80.MHz()).unwrap();

    let rmt_buffer = smartLedBuffer!(1);
    let mut led = SmartLedsAdapter::new(rmt.channel0, led_pin, rmt_buffer);

    let delay = Delay::new();

    let mut color = Hsv {
        hue: 0,
        sat: 255,
        val: 255,
    };
    let mut data;

    info!("Entering main loop");

    loop {
        for hue in 0..=255 {
            let now = time::now();
            // info!("Hello world!, {}", now);

            color.hue = hue;
            // Convert from the HSV color space (where we can easily transition from one
            // color to the other) to the RGB color space that we can then send to the LED
            data = [hsv2rgb(color)];
            // info!("data: {:?}", data);

            // info!("before write");
            // led.write(data.iter().cloned()).unwrap();
            led.write(brightness(gamma(data.iter().cloned()), 10))
                .unwrap();

            delay.delay_millis(20);
        }
    }
}
