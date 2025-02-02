#!/usr/bin/env bash
set -e

direct_boot() {
  cargo build --release

  elf_file="target/riscv32imc-unknown-none-elf/release/hello_world"
  esptool.py \
    --chip esp32-c3 \
    elf2image \
    --flash_size 4MB --flash_mode dio --flash_freq 40m \
    -o out.bin $elf_file

  $OBJDUMP -D $elf_file > disasm.txt

  esptool.py image_info out.bin

  esptool.py \
    --chip esp32-c3 \
    merge_bin \
    --format raw --fill-flash-size 4MB \
    -o merged.bin 0x0000 \
    out.bin
}

bootloader_boot() {
  cargo espflash save-image --chip esp32c3 --merge merged.bin --release
}

direct_boot

QEMU="$(nix build --no-link --print-out-paths ..#qemu)/bin/qemu-system-riscv32"
# QEMU="$HOME/src/qemu/build/qemu-system-riscv32"

	# -s -S \
"$QEMU" \
	-M esp32c3 \
	-drive file=merged.bin,if=mtd,format=raw \
	-global driver=timer.esp32c3.timg,property=wdt_disable,value=true \
	-nographic \
	-semihosting \
	-serial mon:stdio
