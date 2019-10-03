<p align="center">
  <img width="266" height="185" src="docs/tutorial-v1.3/pix/logo.png">
</p>

# Marlowe

This repository contains Marlowe, a domain-specific language (DSL) for describing financial smart contracts that can be enforced by scripts deployed on a blockchain, as well as some tools for analysing and simulating the execution of contracts written in the DSL.

## Learning about Marlowe and Marlowe Playground

The [Marlowe tutorials](./docs/README.adoc) introduce Marlowe and Meadow.

## Version 1.3, stable branch, master branch, and version 2.0

The last stable version of Marlowe can be found in the branch `stable`. This branch currently contains very small improvements with respect to version `1.3` and is the one in which the current version of Meadow is based (see Meadow section below). For the pure version `1.3` you can check the `v1.3` tag. A full description of the `1.3` version was presented at ISoLA 2018, and the paper is available [here](https://iohk.io/research/papers/#2WHKDRA8).

The `master` branch contains the latest developments of Marlowe, version `3.0`.
Versions `1.x`, and `2.0` can be found under `semantics-1.0`, and `semantics-2.0`, respectivly.

## Build on MacOS

Requirements: Homebrew, Haskell Stack 1.6 or later.

Install Haskell Stack if you haven't already

    $ brew install haskell-stack

    $ brew install glpk
    $ stack setup
    $ stack build
