{ compiler ? (import ./.nix/compiler.nix).default
, pkgs ? import ./.nix/nixpkgs.nix { inherit compiler; }
}:

rec {
  inherit pkgs compiler;
  hsPkgs = pkgs.haskell.packages.${compiler};

  dex = pkgs.haskell.lib.overrideCabal (hsPkgs.callCabal2nix "dex" ./. {
  }) (old: {

    doCheck = false;
    doHaddock = false;
  });
}
