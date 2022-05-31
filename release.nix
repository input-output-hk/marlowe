let
  url = "https://github.com/NixOS/nixpkgs/archive/ec6eaba9dfcfdd11547d75a193e91e26701bf7e3.tar.gz";
  pkgs = import (builtins.fetchTarball url) { system = "x86_64-linux"; };
  isabelleNix = import ./isabelle.nix;
  haskellNix = import ./haskell.nix {};
  jobs = {
    isabelle = isabelleNix.isabelleTest;
    haskell = haskellNix.marlowe.components.exes.marlowe ;
  };
in {
  x86_64-linux = jobs;
  required = pkgs.releaseTools.aggregate {
    name = "marlowe";
    constituents = map (x: "x86_64-linux.${x}") (builtins.attrNames jobs);
  };
}
