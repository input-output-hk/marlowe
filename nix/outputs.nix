{ repoRoot, inputs, pkgs, lib, system }:

[
  (
    repoRoot.nix.project.flake
  )

  {
    packages.isabelle-test = repoRoot.nix.isabelle.isabelle-test;
  }

  (lib.optionalAttrs pkgs.stdenv.isLinux {
    hydraJobs.packages = repoRoot.nix.isabelle.isabelle-test;
  }
    ]
