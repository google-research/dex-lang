{ pkgs ? import <nixpkgs> {} }:
pkgs.stdenv.mkDerivation {
  name = "dex";
  buildInputs = with pkgs; [
    cabal-install
    cacert
    clang_12
    git
    haskell.compiler.ghc884
    libpng
    llvm_12
    pkg-config
    stack
    zlib
  ];
}
