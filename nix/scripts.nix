{ pkgs, writeShellScriptBinInRepoRoot }:
{
  build-marlowe-proofs = writeShellScriptBinInRepoRoot "build-marlowe-proofs" ''
    #!/bin/bash
    echo "Building Marlowe proofs"

    # We build hold library (with -b) so that is available in
    # the users HEAP directory for fast rebuilds. In a user
    # machine it only builds the first time, the next time it
    # will see that there are no changes.

    if [ "$1" != "false" ]; then
      echo "Building HOL-Library"
      isabelle build -v -b HOL-Library
    fi

    # We clean the generated files to avoid orphans
    rm -Rf isabelle/generated

    # We build the different sessions that conform the Marlowe specification
    isabelle build -v -b -d isabelle Util
    isabelle build -v -b -d isabelle Core
    isabelle build -v -b -d isabelle Examples
    isabelle build -v -b -e -d isabelle CodeExports
    isabelle build -v -b -d isabelle StaticAnalysis
  '';


  build-marlowe-docs = writeShellScriptBinInRepoRoot "build-marlowe-docs" ''
    #!/bin/bash
    echo "Generating Literate Haskell Tex"
    lhs2TeX isabelle/haskell/MarloweCoreJson.lhs | sed '1,/PATTERN FOR SED/d' > isabelle/Doc/Specification/document/marlowe-core-json.tex

    echo "Building Marlowe docs"
    isabelle document -v -V -d isabelle -P papers Cheatsheet
    isabelle document -v -V -d isabelle -P papers Specification
  '';
  edit-marlowe-proofs = writeShellScriptBinInRepoRoot "edit-marlowe-proofs" ''
    #!/bin/bash
    isabelle jedit -d isabelle -u isabelle/Doc/Specification/Specification.thy
  '';
}
