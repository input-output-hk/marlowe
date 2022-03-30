builtins.mapAttrs (k: _v:
  let
    url = "https://github.com/NixOS/nixpkgs/archive/4358b0fd675c6a0e07140cd85caf1bc18ca80183.tar.gz";
    pkgs = import (builtins.fetchTarball url) { system = k; };
    isabelleNix = import ./isabelle.nix; 
    haskellNix = import ./haskell.nix {}; 
  in
  pkgs.recurseIntoAttrs {
    testIsabelle = isabelleNix.isabelleTest;
    testHaskell = haskellNix.marlowe.components.exes.marlowe ;
  }
) {
  x86_64-linux = {};
}
