#!/usr/bin/env bash

cargo espflash save-image --chip esp32c3 --merge merged.bin --release && nix run ..#qemu merged.bin
