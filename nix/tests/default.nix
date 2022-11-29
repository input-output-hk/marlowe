{ isabelle-pkgs
, scripts
, latex
, pkgs
, src

}: {
  isabelle-test = pkgs.callPackage ./isabelle.nix {
    inherit isabelle-pkgs scripts latex src;
  };
}
