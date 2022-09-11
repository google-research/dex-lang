{
  description = "Dex (named for \"index\") is a research language for typed, functional array processing.";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    llvm-hs-src = {
      url = "github:llvm-hs/llvm-hs/llvm-12";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, llvm-hs-src }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = (import nixpkgs {
        inherit system;
        config.allowUnfree = true; # Needed for CUDA
      });
    in rec {
      packages.dex = (pkgs.callPackage ./. {
        inherit pkgs;
        inherit llvm-hs-src;
      });
      packages.dex-cuda = (pkgs.callPackage ./. {
        inherit pkgs;
        inherit llvm-hs-src;
        withCudaSupport = true;
      });
      defaultPackage = packages.dex;

      devShell = (import ./shell.nix {
        inherit pkgs;
      });
    });
  }
