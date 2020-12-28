{ nixpkgs ? import <nixpkgs> {} }:
with nixpkgs;
stdenv.mkDerivation {
  name = "dex";
  buildInputs = [
    cabal-install
    haskell.compiler.ghc884
    llvm_9
    clang_9
    pkg-config
    libpng
    git
    cacert
  ];
}
