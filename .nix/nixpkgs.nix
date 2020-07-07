{ compiler ? (import ./compiler.nix).default
}:

let
  llvmOverlay = self: super: {
    haskell = super.haskell // {
      packages = super.haskell.packages // {
        "${compiler}" = super.haskell.packages."${compiler}".override {
          overrides = hself: hsuper: with super.haskell.lib; {
            llvm-hs = unmarkBroken (hsuper.llvm-hs_9_0_1.override {
              llvm-config = self.llvm_9;
            });

            llvm-hs-pure = hsuper.llvm-hs-pure_9_0_0;
          };
        };
      };
    };
  };
in import ./pinned-nixpkgs.nix {
  config = {};
  overlays = [ llvmOverlay ];
}
