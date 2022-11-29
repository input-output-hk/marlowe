{ isabelle-pkgs
, scripts
, latex
, pkgs
, src

}: {
  isabelle-test = pkgs.callPackage ./isabelle.nix {
    inherit isabelle-pkgs scripts latex src;
  };
  nixpkgsFmt = pkgs.callPackage ./nixpkgs-fmt.nix {
    inherit src;
    inherit (pkgs) nixpkgs-fmt;
  };
}
