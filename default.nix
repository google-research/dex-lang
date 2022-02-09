{ pkgs ? import <nixpkgs> {},
  llvm-hs-src ? pkgs.fetchFromGitHub {
    owner = "llvm-hs";
    repo = "llvm-hs";
    rev = "llvm-12";
    sha256 = "IG4Mh89bY+PtBJtzlXKYsPljfHP7OSQk03pV6fSmdRY=";
  },
  cudaPackage ? pkgs.cudaPackages.cudatoolkit_11,
  cuda ? false,
  optimized ? true,
  live ? true,
}:
let
  llvm-hs-pure = pkgs.haskellPackages.callCabal2nix "llvm-hs-pure" "${llvm-hs-src}/llvm-hs-pure" {
  };
  llvm-hs = (pkgs.haskellPackages.callCabal2nix "llvm-hs" "${llvm-hs-src}/llvm-hs" {
    inherit llvm-hs-pure;
  }).overrideAttrs (oldAttrs: rec {
    buildInputs = oldAttrs.buildInputs ++ [
      pkgs.llvm_12
    ];
  });
  buildFlags = pkgs.lib.optionals optimized [
    "-foptimized"
  ] ++ pkgs.lib.optionals live [
    "-flive"
  ] ++ pkgs.lib.optionals cuda [
    "-fcuda"
    "--extra-include-dirs=${cudaPackage}/include"
    "--extra-lib-dirs=${cudaPackage}/lib64/stubs"
  ];
  cxxFlags = [
    "-fPIC"
    "-std=c++11"
    "-fno-exceptions"
    "-fno-rtti"
  ] ++ pkgs.lib.optional cuda "-DDEX_CUDA"
    ++ pkgs.lib.optional live "-DDEX_LIVE";
  buildRuntimeCommand =  ''
      ${pkgs.clang_9}/bin/clang++ \
      ${builtins.concatStringsSep " " cxxFlags} \
      -c \
      -emit-llvm  \
      -I${pkgs.libpng}/include \
      src/lib/dexrt.cpp  \
      -o src/lib/dexrt.bc
  '';
in
  # `callCabal2nix` converts `dex.cabal` into a Nix file and builds it.
  # Before we do the Haskell build though, we need to first compile the Dex runtime
  # so it's properly linked in when compiling Dex. Normally the makefile does this,
  # so we instead sneak compiling the runtime in the configuration phase for the Haskell build.
  (pkgs.haskellPackages.callCabal2nix "dex" ./. {
    inherit llvm-hs;
    inherit llvm-hs-pure;
  }).overrideAttrs (attrs: {
    configurePhase = ''
    # Compile the Dex runtime
    echo 'Compiling the Dex runtime...'
    set -x
    ${buildRuntimeCommand}
    set +x
    echo 'Done compiling the Dex runtime.'

    # Run the Haskell configuration phase
    ${attrs.configurePhase}
    '';
    configureFlags = builtins.concatStringsSep " " buildFlags;
    buildInputs = attrs.buildInputs ++ (pkgs.lib.optional cuda
      cudaPackage
    );
  })
