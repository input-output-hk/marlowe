builtins.mapAttrs (k: _v:
  let
    url = "https://github.com/NixOS/nixpkgs/archive/2255f292063ccbe184ff8f9b35ce475c04d5ae69.tar.gz";
    pkgs = import (builtins.fetchTarball url) { system = k; };
    isabelleNix = import ./isabelle.nix; 
    haskellNix = import ./haskell.nix {}; 
  in
  pkgs.recurseIntoAttrs {
    testIsabelle = isabelleNix.isabelleTest;
    testHaskell = haskellNix.marlowe.components.marlowe ;
  }
) {
  x86_64-linux = {};
}
