ENTRY(_start);

MEMORY {
  iram_seg(RX) : ORIGIN = 0x4037C000 + 0x4000, len = 0x64000 - 0x4000
  dram_seg(RW) : ORIGIN = 0x3FC80000, len = 0x60000
  rtc_fast_seg : ORIGIN = 0x50000000, len = 0x2000
}

SECTIONS {
  .stack (NOLOAD) : {
    _stack_end = ABSOLUTE(.);

    /* Adjust stack size here: */
    . = ORIGIN(dram_seg) + 0x8000;

    _stack_start = ABSOLUTE(.);
  } > dram_seg

  .pad.iram (NOLOAD) : {
    . = ORIGIN(iram_seg) + _stack_start - ORIGIN(dram_seg);
  } > iram_seg
  .iram : {
    _iram_start = ABSOLUTE(.);

    # trap
    KEEP(*(.trap));
    *(.trap.*);

    *(.rwtext.literal .rwtext .rwtext.literal.* .rwtext.*)

    KEEP(*(.init));
    KEEP(*(.init.rust));
    KEEP(*(.text.abort));

    *(.literal .text .literal.* .text.*)

    _iram_end = ABSOLUTE(.);
  } > iram_seg

  .pad.data (NOLOAD) : {
    . = ORIGIN(dram_seg) + _iram_end - ORIGIN(iram_seg);
  } > dram_seg
  .data : {
    . = ALIGN(4);
    _data_start = ABSOLUTE(.);

    *(.sdata .sdata.* .sdata2 .sdata2.*);
    *(.data .data.*);
    *(.data1)

    # rodata
    *(.rodata .rodata.*)
    *(.srodata .srodata.*)

    _data_end = ABSOLUTE(.);
  } > dram_seg

  .bss (NOLOAD) : {
    . = ALIGN(4);
    _bss_start = ABSOLUTE(.);

    *(.dynsbss)
    *(.sbss)
    *(.sbss.*)
    *(.gnu.linkonce.sb.*)
    *(.scommon)
    *(.sbss2)
    *(.sbss2.*)
    *(.gnu.linkonce.sb2.*)
    *(.dynbss)
    *(.sbss .sbss.* .bss .bss.*);
    *(.share.mem)
    *(.gnu.linkonce.b.*)
    *(COMMON)

    # noinit
    *(.noinit .noinit.*)

    _bss_end = ABSOLUTE(.);
  } > dram_seg

  .rtc_fast.text : {
    . = ALIGN(4);
    *(.rtc_fast.literal .rtc_fast.text .rtc_fast.literal.* .rtc_fast.text.*)
    . = ALIGN(4);
  } > rtc_fast_seg

  .rtc_fast.data : {
    . = ALIGN(4);
    _rtc_fast_data_start = ABSOLUTE(.);
    *(.rtc_fast.data .rtc_fast.data.*)
    _rtc_fast_data_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > rtc_fast_seg

  .rtc_fast.bss (NOLOAD) : {
    . = ALIGN(4);
    _rtc_fast_bss_start = ABSOLUTE(.);
    *(.rtc_fast.bss .rtc_fast.bss.*)
    _rtc_fast_bss_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > rtc_fast_seg

  .rtc_fast.persistent (NOLOAD) : {
    . = ALIGN(4);
    _rtc_fast_persistent_start = ABSOLUTE(.);
    *(.rtc_fast.persistent .rtc_fast.persistent.*)
    _rtc_fast_persistent_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > rtc_fast_seg

  .heap (NOLOAD) : {
    . = ALIGN(4);
    __heap_start = ABSOLUTE(.);
    . = ORIGIN(dram_seg) + LENGTH(dram_seg);
    __heap_end = ABSOLUTE(.);
  } > dram_seg

  .eh_frame (INFO) : { KEEP(*(.eh_frame)) }
  .eh_frame_hdr (INFO) : { *(.eh_frame_hdr) }
}

PROVIDE(__stack_chk_guard = _stack_end + 4096);

PROVIDE(_max_hart_id = 0);

PROVIDE(UserSoft = DefaultHandler);
PROVIDE(SupervisorSoft = DefaultHandler);
PROVIDE(MachineSoft = DefaultHandler);
PROVIDE(UserTimer = DefaultHandler);
PROVIDE(SupervisorTimer = DefaultHandler);
PROVIDE(MachineTimer = DefaultHandler);
PROVIDE(UserExternal = DefaultHandler);
PROVIDE(SupervisorExternal = DefaultHandler);
PROVIDE(MachineExternal = DefaultHandler);

PROVIDE(ExceptionHandler = DefaultExceptionHandler);

PROVIDE(__post_init = default_post_init);

PROVIDE(_setup_interrupts = default_setup_interrupts);

PROVIDE(_mp_hook = default_mp_hook);

PROVIDE(_start_trap = default_start_trap);

INCLUDE "hal-defaults.x"
INCLUDE "rom-functions.x"
