{ pkgs ? import <nixpkgs> { }
, llvm-hs-src ? pkgs.fetchFromGitHub {
    owner = "llvm-hs";
    repo = "llvm-hs";
    rev = "llvm-12";
    sha256 = "IG4Mh89bY+PtBJtzlXKYsPljfHP7OSQk03pV6fSmdRY=";
  }
, cudaPackage ? pkgs.cudaPackages.cudatoolkit_11
, cudaSupport ? false
, optimized ? true
, live ? true
,
}:
let
  inherit (pkgs.lib) optionals;
  configureFlags =
    optionals optimized [ "-foptimized" ]
    ++ optionals live [ "-flive" ]
    ++ optionals cudaSupport [ "-fcuda" "--extra-include-dirs=${cudaPackage}/include" "--extra-lib-dirs=${cudaPackage}/lib64/stubs" ];
  cxxFlags =
    [ "-fPIC" "-std=c++11" "-fno-exceptions" "-fno-rtti" ]
    ++ pkgs.lib.optionals cudaSupport [ "-DDEX_CUDA" ]
    ++ pkgs.lib.optionals live [ "-DDEX_LIVE" ];
  dexRuntime =
    pkgs.stdenv.mkDerivation {
      name = "dex-runtime";
      src = ./src/lib;
      nativeBuildInputs =
        [ pkgs.clang_9 pkgs.libpng ]
        ++ optionals cudaSupport [ cudaPackage ];
      buildPhase =
        ''
          set -x
          clang++ \
          ${ builtins.concatStringsSep " " cxxFlags } \
          -c \
          -emit-llvm  \
          dexrt.cpp  \
          -o dexrt.bc
          set +x
        '';
      installPhase =
        ''
          mkdir -p $out/src/lib
          cp dexrt.bc $out/src/lib/dexrt.bc
        '';
    };
  patchedSrc =
    pkgs.symlinkJoin {
      name = "src-with-dex-runtime";
      paths = [ ./. dexRuntime ];
    };
  hpkgs =
    pkgs.haskellPackages.override {
      overrides = hself: hsuper: with pkgs.haskell.lib.compose; {
        # FIXME: IFD should probably reducedd
        llvm-hs-pure = doJailbreak (hself.callCabal2nix "llvm-hs-pure" "${llvm-hs-src}/llvm-hs-pure" { });
        llvm-hs = addBuildDepends [ pkgs.llvm_12 ] (hself.callCabal2nix "llvm-hs" "${llvm-hs-src}/llvm-hs" { });
        floating-bits = dontCheck (markUnbroken hsuper.floating-bits);
        dex =
          addBuildDepends [ (pkgs.lib.optional cudaSupport cudaPackage) dexRuntime ]
            (appendConfigureFlags configureFlags (hself.callCabal2nix "dex" patchedSrc { }));
      };
    };
in
hpkgs.dex
