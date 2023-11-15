{ repoRoot, inputs, pkgs, lib, system }:

let

  latex-environment = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      scheme-basic
      ulem
      collection-fontsrecommended
      mathpartir
      stmaryrd
      polytable
      lazylist
      ucs;
  };


  isabelle-pkgs = inputs.isabelle-nixpkgs.legacyPackages;


  isabelle-test = pkgs.stdenv.mkDerivation {
    name = "isabelle-test";

    buildInputs = [
      repoRoot.nix.scripts.build-marlowe-proofs
      repoRoot.nix.scripts.build-marlowe-docs
      isabelle-pkgs.isabelle
      isabelle-pkgs.perl
      isabelle-pkgs.nettools
      latex-environment
    ];

    src = inputs.self + /isabelle;

    installPhase = ''
      export HOME=$TMP 

      mkdir -p $out 
      cd $out
      cp -R $src isabelle
      chmod -R 775 isabelle
      ROOT=.

      mv isabelle/generated isabelle/generated-old

      build-marlowe-proofs false

      if ! diff --recursive --new-file --brief isabelle/generated isabelle/generated-old
      then
        echo "isabelle build generated different files, did you check in isabelle/generated?" >&2
        exit 1
      fi
    
      build-marlowe-docs
    '';
  };
in

{
  inherit (isabelle-pkgs) isabelle perl nettools;
  inherit latex-environment isabelle-test;
}