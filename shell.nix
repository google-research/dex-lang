with (import ./default.nix {});

hsPkgs.shellFor {
  packages = _: [
    dex
  ];

  withHoogle = true;

  buildInputs = with pkgs; [
    cabal-install
    cabal2nix
    ghcid

    llvm_9
    gdb
    lldb
  ];
}
