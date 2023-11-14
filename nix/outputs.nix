{ repoRoot, inputs, pkgs, lib, system }:

let

  project = repoRoot.nix.project;

  isabelle = import ./isabelle.nix { inherit repoRoot inputs pkgs lib system; };

in

[
  project.flake
  {
    packages.isabelle-test = isabelle.isabelle-test;
    hydraJobs.packages.isabelle-test = isabelle.isabelle-test;
  }
]
