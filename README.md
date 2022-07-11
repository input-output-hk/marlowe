<p align="center">
  <img width="266" height="185" src="marlowe-logo.svg">
</p>

# Marlowe

This repository contains the specification of Marlowe, a domain-specific language (DSL) for describing financial smart contracts that can be enforced by scripts deployed on a blockchain, as well as some tools for analysing and simulating the execution of contracts written in the DSL. To use Marlowe on the cardano blockchain please refer to the [marlowe-cardano](https://github.com/input-output-hk/marlowe-cardano) repository

## Learning about Marlowe and its ecosystem

The Cardano Docs has a [section on Marlowe](https://docs.cardano.org/marlowe/learn-about-marlowe) that explains what is marlowe and the different tools available.

## Versions of Marlowe

The `master` branch contains the latest version of Marlowe, version `3`.

An earlier version of Marlowe is described in a [paper](https://iohk.io/research/papers/#2WHKDRA8) that was presented at ISoLA 2018. This version is tagged `v1.3` and a minor update on this is tagged `v1.3.1`.
Versions `1.x`, and `2.0` can also be found in the `master` branch under `semantics-1.0`, and `semantics-2.0`, respectively.

## Developer environment

This repository uses `nix` and `nix-flakes` to provide a reproducible developer environment to all users. Follow the instructions to [install](https://nixos.org/download.html) the nix package manager on your OS and then [use nix to install nix-flakes](https://nixos.wiki/wiki/Flakes#Installing_flakes).

Once both tools are installed, download the repository and get in the development environment using

```bash
$ git clone git@github.com:input-output-hk/marlowe.git
$ cd marlowe
$ nix develop .
```

### Isabelle proofs

To Build the tests, you can run the following command inside the development environment.

```bash
[nix-develop] $ build-marlowe-proofs
```

To open the Isabelle IDE to modify or explore the proofs, use the following command

```bash
[nix-develop] $ edit-marlowe-proofs
```

To generate the specification and cheatsheet pdfs you can use the following command:
```bash
[nix-develop] $ build-marlowe-docs
```

the results will be available in the `papers` folder.
