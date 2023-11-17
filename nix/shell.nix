{ repoRoot, inputs, pkgs, lib, system }:

_cabalProject:

{
  name = "marlowe";

  welcomeMessage = ''
    Welcome to Marlowe!

    Tests:
      • run-isabelle-test
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
      • perl
  '';

  packages = [
    repoRoot.nix.isabelle.isabelle
    repoRoot.nix.isabelle.latex-environment
    repoRoot.nix.isabelle.perl
    repoRoot.nix.isabelle.nettools

    repoRoot.nix.scripts.run-isabelle-test
    repoRoot.nix.scripts.build-marlowe-proofs
    repoRoot.nix.scripts.edit-marlowe-proofs
    repoRoot.nix.scripts.build-marlowe-docs
    repoRoot.nix.scripts.generate-marlowe-language-specification

    pkgs.haskellPackages.lhs2tex
    pkgs.haskellPackages.BNFC

    pkgs.nil
    pkgs.tk
  ];

  preCommit = {
    nixpkgs-fmt.enable = true;
  };
}
