{ repoRoot, inputs, pkgs, lib, system }:

let

  latex = (pkgs.texlive.combine {
    inherit (pkgs.texlive) scheme-basic ulem collection-fontsrecommended mathpartir stmaryrd polytable lazylist ucs;
  });

  writeShellScriptBinInRepoRoot = name: script: pkgs.writeShellScriptBin name ''
    cd `${pkgs.git}/bin/git rev-parse --show-toplevel`
    ${script}
  '';

  scripts = import ./scripts.nix { inherit pkgs writeShellScriptBinInRepoRoot; };

  isabelle-pkgs = inputs.isabelle-nixpkgs.legacyPackages.${system};

  isabelle-test = { src }: isabelle-pkgs.runCommand
    "isabelle-test"
    {
      nativeBuildInputs =
        (with scripts; [
          build-marlowe-proofs
          build-marlowe-docs
        ]) ++
        [ isabelle-pkgs.isabelle isabelle-pkgs.perl isabelle-pkgs.nettools latex ];
      src = "${src}/isabelle";
    }
    ''
      export HOME=$TMP
      unpackPhase
      mv isabelle/generated isabelle/generated-old
      build-marlowe-proofs false
      if ! diff --recursive --new-file --brief isabelle/generated isabelle/generated-old
      then
        echo "isabelle build generated different files, did you check in isabelle/generated?" >&2
        exit 1
      fi
    
      build-marlowe-docs
    
      touch $out
    '';

in

{
  inherit (isabelle-pkgs) isabelle perl nettools;
  inherit scripts latex;
  isabelle-test = pkgs.callPackage isabelle-test { src = inputs.self; };
}
