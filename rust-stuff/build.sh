#!/usr/bin/env bash

rustc \
    --target riscv32imc-unknown-none-elf \
    --crate-type=staticlib \
    -Cpanic=abort \
    -Clinker-plugin-lto \
    -o libxyz.a \
    test.rs

rm -rf ext
mkdir ext
$AR --output ext x libxyz.a