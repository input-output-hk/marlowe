{ repoRoot, inputs, pkgs, lib, system }:

cabalProject:

let

  isabelle = import ./isabelle.nix { inherit repoRoot inputs pkgs lib system; };

in

{
  name = "marlowe";
  welcomeMessage = ''
    Welcome to Marlowe!

    Tests:
      • isabelle-test
      • cabal test all
    Scripts:
      • build-marlowe-proofs
      • edit-marlowe-proofs
      • build-marlowe-docs
      • generate-marlowe-language-specification
    Tools:
      • bnfc
      • isabelle
      • latex
      • lhs2tex
      • nettools
      • nil
      • perl'';
  packages = [
    isabelle.isabelle-test
    isabelle.scripts.build-marlowe-proofs
    isabelle.scripts.edit-marlowe-proofs
    isabelle.scripts.build-marlowe-docs
    isabelle.scripts.generate-marlowe-language-specification
    isabelle.isabelle
    isabelle.latex
    isabelle.perl
    isabelle.nettools
    pkgs.nil
    pkgs.haskellPackages.lhs2tex
    pkgs.haskellPackages.BNFC
  ];
  preCommit = {
    nixpkgs-fmt.enable = true;
  };
}
