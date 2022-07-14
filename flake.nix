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
        isabelle build -v -d isabelle Marlowe
      '';
      edit-marlowe-proofs = writeShellScriptBinInRepoRoot "edit-marlowe-proofs" ''
        #!/bin/bash
        isabelle jedit -u isabelle/Semantics.thy isabelle/MoneyPreservation.thy isabelle/StaticAnalysis.thy isabelle/TransactionBound.thy isabelle/CloseSafe.thy
      '';
      latex = (pkgs.texlive.combine {
          inherit (pkgs.texlive) scheme-basic ulem collection-fontsrecommended mathpartir;
      });
      project = pkgs.haskell-nix.cabalProject' {
        src = ./.;
        compiler-nix-name = "ghc923";
        shell.tools.cabal = {};
        shell.inputsFrom = [ self.packages.${system}.isabelle-test ];
        shell.nativeBuildInputs = [build-marlowe-proofs edit-marlowe-proofs latex];
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
