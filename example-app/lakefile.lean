import Lake
open Lake DSL

package «example» where
  -- backend := .llvm

  -- Build start.o with:
  -- $CC -c start.c
  moreLinkArgs := #["-Wl,--allow-multiple-definition", "start.o"]

lean_lib «Peripherals» where
  -- add library configuration options here

@[default_target]
lean_exe «example» where
  root := `Main
