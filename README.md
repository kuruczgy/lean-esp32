# Lean on the ESP32-C3

This is a proof-of-concept project for running Lean code on the [ESP32-C3](https://www.espressif.com/en/products/socs/esp32-c3), a RISC-V microcontroller with 384 KiB of RAM.

## How it works

Summary in a few bullet points:

- The Lean compiler and standard library are unmodified, though the library initialization is stubbed out to reduce code size.
- There is a [slimmed down Lean runtime located in this repo](/platform/runtime).
- [Picolibc](https://github.com/picolibc/picolibc) and [libc++](https://libcxx.llvm.org/) are used as the standard C and C++ libraries respectively.
- No pre-compiled toolchain, binary blobs, bootloader, or anything from [ESP-IDF](https://github.com/espressif/esp-idf) is used, everything is defined in [`flake.nix`](/flake.nix) and compiled from source (or comes from the NixOS cache).
- Everything fits into RAM, including the code and the heap.

## Building and running

The only tool you need is Nix (with flakes enabled), everything else is managed through it. (Tested on `x86_64-linux` and `aarch64-linux`.)

Run `nix build .#example-app`. `result/main.bin` can be flashed onto an ESP32-C3 device that has a WS2812 compatible LED connected to GPIO 10. (I used the [Waveshare ESP32-C3-Zero](https://www.waveshare.com/wiki/ESP32-C3-Zero) development board.)

Alternately, you can run `nix run .#qemu` to run the example application in QEMU. (Note that this will create a temporary image file at `/tmp/merged-flash.bin`.)

## Development

1. Run `nix develop` to enter a development shell.
2. If your editor supports using Lean and/or clangd, you can open it from this devshell to have it use the correct versions of those. For using clangd, run `ln -s $compile_flags compile_flags.txt` to set up the compiler flags. This should work for all C/C++ files found in this project. (In particular, this was tested with VSCode with the [clangd](https://marketplace.visualstudio.com/items?itemName=llvm-vs-code-extensions.vscode-clangd) and [lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) extensions.)
3. Enter the `example-app` directory.
4. Make modifications to `Main.lean`
5. Run `eval "$buildPhase"` to compile the app. (Note that the compilation of `start.c` is not hooked up to Lake yet, and modifications might not get picked up. Delete the `.lake` directory and recompile after you modify `start.c`.)
6. Run `out=. eval "$installPhase"` to generate `main.bin` in the current directory.
7. Run `esptool.py --port /dev/ttyACM0 --no-stub load_ram main.bin` to load the program to RAM and execute it. (Substitute `/dev/ttyACM0` appropriately.)
8. Go to step 4.
