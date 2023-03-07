{
  description = "Dex (named for \"index\") is a research language for typed, functional array processing.";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    llvm-hs-src = {
      url = "github:llvm-hs/llvm-hs/llvm-12";
      flake = false;
    };
  };
  outputs =
    { self
    , nixpkgs
    , flake-utils
    , llvm-hs-src
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      unfreePkgs = import nixpkgs {
        inherit system;
        # NOTE: Needed for CUDA
        config.allowUnfree = true;
      };
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      packages = rec {
        dex = import ./. { inherit pkgs llvm-hs-src; };
        dex-cuda =
          import ./. {
            inherit llvm-hs-src;
            pkgs = unfreePkgs;
            cudaSupport = true;
          };
        default = dex;
      };
      devShells.default = import ./shell.nix { inherit pkgs; };
      formatter = pkgs.nixpkgs-fmt;
    }
    );
}
