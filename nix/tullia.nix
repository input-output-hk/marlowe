/*
This file defines tullia tasks and cicero actions.
Tullia is a sandboxed multi-runtime DAG task runner with Cicero support.
Tasks can be written in different languages and are compiled for each runtime using Nix.
It comes with essential building blocks for typical CI/CD scenarios.
Learn more: https://github.com/input-output-hk/tullia
Cicero is an if-this-then-that machine on HashiCorp Nomad.
It can run any event-and-state-driven automation actions
and hence CI/CD pipelines are a natural fit.
In tandem with Tullia, an action could be described as
the rule that describes when a Tullia task is to be invoked.
Learn more: https://github.com/input-output-hk/cicero
*/

let
  ciInputName = "GitHub event";
  repository = "input-output-hk/marlowe";
  ciTaskTopAttr = "hydraJobs";

in rec {
  tasks.ci = {config, lib, ...}: {
    preset = {
      nix.enable = true;

      github.status = {
        enable = config.actionRun.facts != {};
        inherit repository;
        revision = config.preset.github.lib.readRevision ciInputName null;
      };
    };

    command.text = let
      flakeUrl = ''github:${repository}/"$(${lib.escapeShellArg config.preset.github.status.revision})"'';
    in config.preset.github.status.lib.reportBulk {
      bulk.text = ''
        echo '["x86_64-linux", "x86_64-darwin"]' | nix-systems -i
      '';
      each.text = ''nix build -L ${flakeUrl}#${lib.escapeShellArg ciTaskTopAttr}."$1".required'';
      skippedDescription = lib.escapeShellArg "No nix builder available for this platform";
    };

    # some hydra jobs run NixOS tests
    env.NIX_CONFIG = ''
      extra-system-features = kvm
    '';

    memory = 1024 * 32;
    nomad.resources.cpu = 10000;
  };

  actions = {
    "marlowe/ci" = {
      task = "ci";
      io = ''
        let github = {
          #input: "${ciInputName}"
          #repo: "${repository}"
        }
        #lib.merge
        #ios: [
          #lib.io.github_push & github,
          { #lib.io.github_pr, github, #target_default: false },
      '';
    };

  };
}
