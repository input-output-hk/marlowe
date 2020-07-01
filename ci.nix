builtins.mapAttrs (k: _v:
  let
    url = "https://github.com/NixOS/nixpkgs/archive/2255f292063ccbe184ff8f9b35ce475c04d5ae69.tar.gz";
    pkgs = import (builtins.fetchTarball url) { system = k; };
    haskellNix = import (builtins.fetchTarball "https://github.com/input-output-hk/haskell.nix/archive/master.tar.gz") {};
    haskellNixPkgs = import haskellNix.sources.nixpkgs-2003 haskellNix.nixpkgsArgs;
    isabelleNix = import ./isabelle.nix; 
  in
  pkgs.recurseIntoAttrs {
    testIsabelle = isabelleNix.isabelleTest;
    testHaskell = pkgs.haskell-nix.project {
      src = pkgs.haskell-nix.haskellLib.cleanGit {
        name = "marlowe";
        src = ./.;
      };
    };
  }
) {
  x86_64-linux = {};
}
