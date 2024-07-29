ENTRY(call_start_cpu0);

MEMORY {
  iram_seg(RX) : ORIGIN = 0x4037C000 + 0x4000, len = 0x64000 - 0x4000
  dram_seg(RW) : ORIGIN = 0x3FC80000, len = 0x60000
}

SECTIONS {
  .stack (NOLOAD) : {
    /* Adjust stack size here: */
    . = ORIGIN(dram_seg) + 0x8000;
    _stack_end = ABSOLUTE(.);
  } > dram_seg

  .pad.iram (NOLOAD) : {
    . = ORIGIN(iram_seg) + _stack_end - ORIGIN(dram_seg);
  } > iram_seg
  .iram : {
    _iram_start = ABSOLUTE(.);
    KEEP(*(.entry.text))
    *(.text)
    *(.text*)
    KEEP(*(.init))
    KEEP(*(.fini))
    *(__lcxx_override)
    _iram_end = ABSOLUTE(.);
  } > iram_seg

  .pad.data (NOLOAD) : {
    . = ORIGIN(dram_seg) + _iram_end - ORIGIN(iram_seg);
  } > dram_seg
  .data : {
    . = ALIGN(4);
    _data_start = ABSOLUTE(.);
    *(.rodata)
    *(.rodata*)
    *(.data)
    *(.data*)
    _data_end = ABSOLUTE(.);
  } > dram_seg

  .bss (NOLOAD) : {
    . = ALIGN(4);
    _bss_start = ABSOLUTE(.);
    *(.bss)
    *(.bss*)
    *(.sbss)
    *(COMMON)
    _bss_end = ABSOLUTE(.);
  } > dram_seg

  .heap (NOLOAD) : {
    . = ALIGN(4);
    __heap_start = ABSOLUTE(.);
    . = ORIGIN(dram_seg) + LENGTH(dram_seg);
    __heap_end = ABSOLUTE(.);
  } > dram_seg
}
