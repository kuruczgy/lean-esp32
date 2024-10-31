{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  outputs = { self, nixpkgs }:
    let
      eachDefaultSystem = f: builtins.zipAttrsWith
        (_: nixpkgs.lib.listToAttrs)
        (map
          (system: builtins.mapAttrs
            (_: nixpkgs.lib.nameValuePair system)
            (f system))
          nixpkgs.lib.systems.flakeExposed);
    in
    eachDefaultSystem (system:
      let
        pkgsNative = nixpkgs.legacyPackages.${system};

        # Nixpkgs needs some minor patches to get cross-compilation working properly.
        nixpkgs-patched = pkgsNative.applyPatches {
          name = "nixpkgs-patched";
          src = nixpkgs;
          patches = [ ./patches/nixpkgs.patch ];
        };

        # Nixpkgs only has newlib, not picolibc, so we have to package it.
        picolibc-pkg = { stdenv, lib, fetchFromGitHub, buildPackages }: stdenv.mkDerivation rec {
          pname = "picolibc";
          version = "1.8.6";
          src = fetchFromGitHub {
            owner = pname;
            repo = pname;
            rev = version;
            hash = "sha256-5W/+vorhOP/MD19JYzHJfZTkWMM7sKUQqzTDA/7rxZs=";
          };
          nativeBuildInputs = [ buildPackages.meson buildPackages.ninja ];
          mesonFlags = [
            "-Dmultilib=false"
            "-Dformat-default=minimal"

            # TODO: can't these be disabled?
            "-Dnewlib-locale-info=true"
            "-Dnewlib-locale-info-extended=true"
          ];
          NIX_CFLAGS_COMPILE = [ "-Qunused-arguments" "-nodefaultlibs" ];
        };

        lean4-runtime-pkg = { stdenv, cmake, buildPackages }: stdenv.mkDerivation {
          pname = "lean4-runtime";
          version = buildPackages.lean4.version;
          src = buildPackages.lean4.src;
          preConfigure = ''
            # Use the runtime sources from this repo.
            rm -r src/runtime
            ln -s ${./platform/runtime} src/runtime
            ln -sf ${./platform/lean/lean.h} src/include/lean/lean.h

            # Use the CMakeLists.txt from src instead of the root directory.
            cd src
          '';
          installPhase = ''
            mkdir -p $out/lib
            cp lib/lean/libleanrt.a $out/lib/
            cp -r include $out/
          '';
          cmakeFlags = [
            "-DSTAGE=1"
            "-DUSE_GMP=OFF"
            "-DMULTI_THREAD=OFF"
            "-DSMALL_ALLOCATOR=OFF"
          ];
          buildFlags = [ "leanrt" ];
          nativeBuildInputs = [ cmake ];
          NIX_CFLAGS_COMPILE = [
            "-nostdlib++"
            "-ffunction-sections"
          ];
        };

        # Basically the only thing this does is make lean use stdenv cc-wrapper
        # instead of its own custom leanc wrapper. With this hacky overlay, we
        # can avoid having to rebuild lean.
        lean4-stdenv-cc-pkg = { stdenv, symlinkJoin, lean4, targetPackages }: symlinkJoin {
          name = "lean4-stdenv-cc";
          paths = [ lean4 ];
          postBuild = ''
            # Lake uses its own executable path to figure out the lean install
            # location, so copy it instead of symlinking.
            rm $out/bin/lake
            cp ${lean4}/bin/lake $out/bin

            # Replace leanc with a symlink directly to the stdenv cc-wrapper.
            rm $out/bin/leanc
            ln -s "${targetPackages.stdenv.cc}/bin/${targetPackages.stdenv.cc.targetPrefix}clang" $out/bin/leanc

            # leanmake is not patched properly in nixpkgs, fix it here.
            rm $out/share/lean/lean.mk
            sed 's|/usr/bin/env||' ${lean4}/share/lean/lean.mk > $out/share/lean/lean.mk
          '';
        };

        lean4-init-pkg = { stdenv, buildPackages, lean4-runtime }: stdenv.mkDerivation {
          pname = "lean4-init";
          version = buildPackages.lean4.version;
          src = buildPackages.lean4.src;
          nativeBuildInputs = [ buildPackages.lean4-stdenv-cc ];
          buildPhase = ''
            cd src
            leanmake -j$NIX_BUILD_CORES lib PKG=Init
          '';
          installPhase = ''
            mkdir -p $out/lib 
            cp build/lib/libInit.a $out/lib/
          '';
          NIX_CFLAGS_COMPILE = [
            "-nostdlib++"
            "-ffunction-sections"
            "-I${lean4-runtime}/include"
          ];
        };

        # A nix package set to cross compile from x86_64-linux to the esp32-c3.
        # In theory all packages in this package set are meant to be run on the
        # esp32-c3, though for obvious reasons only a select few will actually
        # work.
        pkgs = import nixpkgs-patched {
          localSystem = system;
          crossSystem = {
            # The target triple.
            config = "riscv32-none-elf";

            # The specific RISC-V variant supported by the esp32-c3.
            gcc.arch = "rv32imczicsr";

            # This does not do really do anything since we directly override
            # libcCross to point to picolibc, but let's just set it anyway.
            libc = "picolibc";

            # Make the stdenv use clang instead of gcc.
            useLLVM = true;
          };

          # Disable all hardening flags, since some can inadvertently increase code size.
          config.replaceCrossStdenv = { buildPackages, baseStdenv }: baseStdenv.override (_: {
            cc = buildPackages.llvmPackages_18.tools.clang.override (old: {
              bintools = old.bintools.override (_: {
                defaultHardeningFlags = [ ];
              });
            });
          });

          overlays = [
            (self: super: {
              picolibc = self.callPackage picolibc-pkg {
                stdenv = self.overrideCC self.stdenv
                  self.buildPackages.llvmPackages_18.tools.clangNoLibc;
              };

              libcCross = self.targetPackages.picolibc;

              lean4-runtime = self.callPackage lean4-runtime-pkg { };
              lean4-stdenv-cc = self.callPackage lean4-stdenv-cc-pkg { };
              lean4-init = self.callPackage lean4-init-pkg { };
            })
          ];
        };
      in
      {
        packages = {
          qemu = (pkgsNative.qemu.override {
            hostCpuTargets = [ "xtensa-softmmu" "riscv32-softmmu" ];
          }).overrideAttrs (finalAttrs: {
            version = "9.0.0";
            src = pkgsNative.fetchFromGitHub {
              owner = "espressif";
              repo = "qemu";
              rev = "esp-develop-9.0.0-20240606";

              forceFetchGit = true;
              postFetch = ''
                cd $out
                subprojects="keycodemapdb libvfio-user berkeley-softfloat-3 berkeley-testfloat-3"
                for sp in $subprojects; do
                  ${pkgsNative.meson}/bin/meson subprojects download $sp
                done
                rm -r subprojects/*/.git
              '';
              hash = "sha256-yJ54S+HB3CH5/wb+GFwNkz3/990J8Z6GbuttDhWqN5Q=";
            };
            patches = finalAttrs.patches ++ [ ./patches/qemu.patch ];
            buildInputs = finalAttrs.buildInputs ++ [ pkgsNative.libgcrypt ];
            configureFlags = finalAttrs.configureFlags ++ [ "--enable-gcrypt" ];
          });

          example-app = pkgs.stdenv.mkDerivation {
            name = "example-app";
            src = ./example-app;
            nativeBuildInputs = [
              pkgs.buildPackages.esptool
              pkgs.buildPackages.lean4-stdenv-cc
            ];
            buildPhase = ''
              $CC --compile start.c
              lake build
            '';
            installPhase = ''
              mkdir -p $out
              esptool.py \
                --chip esp32-c3 \
                elf2image \
                --flash_size 4MB --flash_mode dio --flash_freq 40m \
                -o $out/main.bin .lake/build/bin/example
            '';
            NIX_CFLAGS_COMPILE = [
              # Hack because clang adds -lunwind as well for some reason by default
              # TODO: see if --remap-inputs can be used instead?
              "-nostdlib++"
              "-lc"
              "-lc++"

              # TODO: it's broken without this, isn't -O2 the default??
              "-O2"

              # Linker flags
              "-Wl,-T${./platform/esp32-c3.ld}"
              "-Wl,--gc-sections"
              "-ffunction-sections"

              # Lean include path and libraries
              "-I${pkgs.lean4-runtime}/include"
              "-L${pkgs.lean4-runtime}/lib"
              "-lleanrt"

              "-L${pkgs.lean4-init}/lib"
              "-lInit"
            ];
          };
          default = self.packages.${system}.example-app;
        };

        devShells.default = self.packages.${system}.example-app.overrideAttrs (old: {
          nativeBuildInputs = old.nativeBuildInputs ++ [
            self.packages.${system}.qemu
            pkgs.buildPackages.llvmPackages_18.tools.clang-tools
          ];
          compile_flags = pkgsNative.writeText "compile_flags.txt" ''
            -target
            riscv32-none-elf
            -xc++
            -Iplatform
            -I${pkgs.lean4-runtime}/include
          '';
        });

        apps =
          let
            main-bin = "${self.packages.${system}.example-app}/main.bin";
          in
          pkgs.lib.mapAttrs (k: v: { type = "app"; program = "${pkgsNative.writeShellScript k v}"; }) {
            load-to-ram = ''
              ${pkgsNative.esptool}/bin/esptool.py \
                --port ''${1:-/dev/ttyACM0} \
                --no-stub load_ram \
                ${main-bin}
            '';
            flash = ''
              ${pkgsNative.esptool}/bin/esptool.py \
                --port ''${1:-/dev/ttyACM0} \
                write_flash \
                0x0 ${main-bin}
            '';
            qemu = ''
              set -e
              ${pkgsNative.esptool}/bin/esptool.py \
                --chip esp32-c3 \
                merge_bin \
                --format raw --fill-flash-size 4MB \
                -o /tmp/merged-flash.bin 0x0000 \
                ${main-bin}
              ${self.packages.${system}.qemu}/bin/qemu-system-riscv32 \
                -M esp32c3 \
                -drive file=/tmp/merged-flash.bin,if=mtd,format=raw \
                -drive file=/dev/null,if=none,format=raw,id=efuse \
                -global driver=nvram.esp32c3.efuse,property=drive,value=efuse \
                -global driver=timer.esp32c3.timg,property=wdt_disable,value=true \
                -nographic \
                -semihosting \
                -serial mon:stdio
            '';
          };
      });
}
