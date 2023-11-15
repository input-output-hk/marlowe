{ repoRoot, inputs, pkgs, lib, system }:

[
  (
    repoRoot.nix.project.flake
  )

  {
    packages.isabelle-test = repoRoot.nix.isabelle.isabelle-test;
    hydraJobs.packages.isabelle-test = repoRoot.nix.isabelle.isabelle-test;
  }
]
