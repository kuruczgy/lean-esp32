#![no_std]
#![no_main]

use esp_backtrace as _;
use esp_hal::{delay::Delay, main, time};
use log::info;

#[main]
fn main() -> ! {
    // QEMU quirk
    unsafe { (0x6002_3000 as *mut u32).write_volatile(1 << 30) };

    // let conf_val = unsafe { (0x6002_3000 as *mut u32).read_volatile() };
    // println!("systimer conf: {:#x}", conf_val);

    let _ = esp_hal::init(esp_hal::Config::default());

    esp_println::logger::init_logger_from_env();

    let delay = Delay::new();
    loop {
        let now = time::now();
        info!("Hello world!, {}", now);
        delay.delay_millis(500);
    }
}
