{ pkgs ? import <nixpkgs> { }
}:
pkgs.mkShell
{
  buildInputs =
    with pkgs; [ cabal-install cacert clang_12 git haskellPackages.ghc libpng llvm_12 pkg-config stack zlib ];
}
