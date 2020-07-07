{ config ? {}
, overlays ? []
}:

with {
  owner = "NixOS";
  repo = "nixpkgs-channels";
  rev = "41aa2272feb21b1300b9f99de3f8371a6ddd8986";
  sha256 = "0qj3x0jcsz3lbia93a06dzvp2psayxxqxly62kjmsywvsm0picby";
};

import (builtins.fetchTarball {
  url = "https://github.com/${owner}/${repo}/archive/${rev}.tar.gz";
  inherit sha256;
}) { inherit config overlays; }
