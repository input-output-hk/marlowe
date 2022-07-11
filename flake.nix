{
  description = "The Marlowe language";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";

    haskellNix.url = "github:input-output-hk/haskell.nix";

    nixpkgs.follows = "haskellNix/nixpkgs-unstable";

    isabelle-nixpkgs.url = "nixpkgs/nixos-22.05";
    # texlive-nixpkgs.url = "nixpkgs/nixos-22.05";
  };


  outputs = { self, flake-utils, nixpkgs, haskellNix, isabelle-nixpkgs }: let
    inherit (flake-utils.lib) eachSystem system;

    supportedSystems = [ system.x86_64-linux system.x86_64-darwin ];

    base = eachSystem supportedSystems (system: let
      overlays = [ haskellNix.overlay ];

      pkgs = import nixpkgs { inherit system overlays; inherit (haskellNix) config; };

      isabelle-pkgs = isabelle-nixpkgs.legacyPackages.${system};

      writeShellScriptBinInRepoRoot = name: script: pkgs.writeShellScriptBin name ''
        cd `${pkgs.git}/bin/git rev-parse --show-toplevel`
        ${script}
      '';
      build-marlowe-proofs = writeShellScriptBinInRepoRoot "build-marlowe-proofs" ''
        #!/bin/bash
        echo "Building Marlowe proofs"

        # We build hold library (with -b) so that is available in
        # the users HEAP directory for fast rebuilds. In a user
        # machine it only builds the first time, the next time it
        # will see that there are no changes.
        isabelle build -v -b HOL-Library

        # We build the different sessions that conform the Marlowe specification
        isabelle build -v -b -d isabelle Util
        isabelle build -v -b -d isabelle Core
        isabelle build -v -b -d isabelle StaticAnalysis
      '';

      build-marlowe-docs = writeShellScriptBinInRepoRoot "build-marlowe-docs" ''
        #!/bin/bash
        echo "Building Marlowe docs"
        isabelle document -v -V -d isabelle -P papers Cheatsheet
        isabelle document -v -V -d isabelle -P papers Specification
      '';

      edit-marlowe-proofs = writeShellScriptBinInRepoRoot "edit-marlowe-proofs" ''
        #!/bin/bash
        isabelle jedit -d isabelle -u isabelle/Doc/Specification/Specification.thy
      '';
      latex = (pkgs.texlive.combine {
          inherit (pkgs.texlive) scheme-basic ulem collection-fontsrecommended mathpartir;
      });
      project = pkgs.haskell-nix.cabalProject' {
        src = ./.;
        compiler-nix-name = "ghc923";
        shell.tools.cabal = {};
        shell.inputsFrom = [ self.packages.${system}.isabelle-test ];
        shell.nativeBuildInputs = [build-marlowe-proofs edit-marlowe-proofs build-marlowe-docs latex];
      };

      flake = project.flake {};
    in flake // {
      packages = flake.packages // {
        isabelle-test = isabelle-pkgs.runCommand "isabelle-test" {
          nativeBuildInputs = [ isabelle-pkgs.isabelle isabelle-pkgs.perl isabelle-pkgs.nettools latex ];
          src = ./isabelle;
        } ''
          export HOME=$TMP
          unpackPhase
          cd isabelle
          isabelle build -v -d. Marlowe
          touch $out
        '';
      };
      hydraJobs = self.packages.${system};
    });
  in base // {
    hydraJobs = base.hydraJobs // {
      required = nixpkgs.legacyPackages.x86_64-linux.releaseTools.aggregate {
        name = "marlowe";
        constituents = builtins.concatMap (system: map (x: "${x}.${system}") (builtins.attrNames base.hydraJobs)) supportedSystems;
      };
    };
  };
}
