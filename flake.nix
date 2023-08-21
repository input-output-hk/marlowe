{
  description = "The Marlowe language";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";

    haskellNix.url = "github:input-output-hk/haskell.nix";

    nixpkgs.follows = "haskellNix/nixpkgs-unstable";

    isabelle-nixpkgs.url = "nixpkgs/nixos-22.05";

    nixLsp.url = "github:oxalica/nil";

    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";

  };


  outputs = { self, flake-utils, nixpkgs, haskellNix, isabelle-nixpkgs, pre-commit-hooks, nixLsp }:
    let
      inherit (flake-utils.lib) eachSystem system;

      supportedSystems = [ system.x86_64-linux system.x86_64-darwin ];

      base = { evalSystem ? null }: eachSystem supportedSystems (system:
        let evalSystem' = if evalSystem == null then system else evalSystem; in
        let
          evalSystem = evalSystem';

          overlays = [ haskellNix.overlay nixLsp.overlays.nil ];

          pkgs = import nixpkgs { inherit system overlays; inherit (haskellNix) config; };

          isabelle-pkgs = isabelle-nixpkgs.legacyPackages.${system};

          writeShellScriptBinInRepoRoot = name: script: pkgs.writeShellScriptBin name ''
            cd `${pkgs.git}/bin/git rev-parse --show-toplevel`
            ${script}
          '';

          scripts = import ./nix/scripts.nix { inherit pkgs writeShellScriptBinInRepoRoot; };

          formatting = import ./nix/formatting.nix {
            inherit writeShellScriptBinInRepoRoot pkgs;
          };

          latex = (pkgs.texlive.combine {
            inherit (pkgs.texlive) scheme-basic ulem collection-fontsrecommended mathpartir stmaryrd polytable lazylist ucs;
          });

          project = pkgs.haskell-nix.cabalProject' {
            src = ./.;
            compiler-nix-name = "ghc924";
            inherit evalSystem;
            shell.tools.cabal = { inherit evalSystem; };
            shell.tools.haskell-language-server = { inherit evalSystem; };
            shell.shellHook = ''
              ${pre-commit-check.shellHook}

              # The green prompt familiar to those used to nix-shell
              export PS1="\n\[\033[1;32m\][nix develop:\w]\$\[\033[0m\] "
            '';
            shell.inputsFrom = [ packages.isabelle-test ];
            shell.nativeBuildInputs =
              (with scripts; [
                build-marlowe-proofs
                edit-marlowe-proofs
                build-marlowe-docs
                generate-marlowe-language-specification
              ]
              ) ++
              (with pkgs; [
                nil
                haskellPackages.lhs2tex
                haskellPackages.BNFC
              ]) ++
              [ latex formatting.fix-nix-fmt ];
          };

          flake = project.flake { };

          tests = import ./nix/tests {
            src = ./.;
            inherit pkgs isabelle-pkgs scripts latex;
          };

          pre-commit-check = pre-commit-hooks.lib.${system}.run {
            src = (pkgs.lib.cleanSource ./.);
            hooks = {
              nixpkgs-fmt.enable = true;
            };
          };
          packages = flake.packages // {
            inherit (tests) isabelle-test nixpkgsFmt;
          };
        in
        flake // {
          inherit packages;
          hydraJobs = packages;
        }
      );
      hydraSystem = "x86_64-linux";
      pkgsHydra = nixpkgs.legacyPackages.${hydraSystem};
      baseHydra = base { evalSystem = hydraSystem; };
    in
    base { } // {
      hydraJobs = baseHydra.hydraJobs // {
        forceNewEval = pkgsHydra.writeText "forceNewEval" (self.rev or self.lastModified);
        required = pkgsHydra.releaseTools.aggregate {
          name = "marlowe";
          constituents = builtins.concatMap (system: map (x: "${x}.${system}") (builtins.attrNames baseHydra.hydraJobs)) supportedSystems;
        };
      };
    };

  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
    accept-flake-config = true;
  };
}
