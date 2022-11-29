{
  isabelle-pkgs
  , scripts
  , latex
  , src
}: isabelle-pkgs.runCommand "isabelle-test"
              {
                nativeBuildInputs =
                  ( with scripts; [
                      build-marlowe-proofs
                      build-marlowe-docs
                  ]) ++
                  [ isabelle-pkgs.isabelle isabelle-pkgs.perl isabelle-pkgs.nettools latex ];
                src = "${src}/isabelle";
              } ''
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
            ''