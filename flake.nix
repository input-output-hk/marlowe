{
  description = "The Marlowe language";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";

    haskellNix.url = "github:input-output-hk/haskell.nix";

    nixpkgs.follows = "haskellNix/nixpkgs-unstable";

    isabelle-nixpkgs.url = "nixpkgs/nixos-22.05";
  };

  outputs = { self, flake-utils, nixpkgs, haskellNix, isabelle-nixpkgs }: let
    inherit (flake-utils.lib) eachSystem system;

    supportedSystems = [ system.x86_64-linux /*system.x86_64-darwin*/ ];

    base = eachSystem supportedSystems (system: let
      overlays = [ haskellNix.overlay ];

      pkgs = import nixpkgs { inherit system overlays; inherit (haskellNix) config; };

      isabelle-pkgs = isabelle-nixpkgs.legacyPackages.${system};

      project = pkgs.haskell-nix.cabalProject' {
        src = ./.;
        compiler-nix-name = "ghc923";
        shell.tools.cabal = {};
        shell.inputsFrom = [ self.packages.${system}.isabelle-test ];
      };

      flake = project.flake {};
    in flake // {
      packages = flake.packages // {
        isabelle-test = isabelle-pkgs.runCommand "isabelle-test" {
          nativeBuildInputs = [ isabelle-pkgs.isabelle isabelle-pkgs.perl ] ++ isabelle-pkgs.lib.optional (!isabelle-pkgs.stdenv.isDarwin) isabelle-pkgs.nettools;
          src = ./isabelle;
        } ''
          export HOME=$TMP
          unpackPhase
          cd isabelle
          isabelle build -v -d. Test
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
