<p align="center">
  <img width="266" height="185" src="docs/tutorial-v1.3/pix/logo.png">
</p>

# Marlowe

This repository contains Marlowe, a domain-specific language (DSL) for describing financial smart contracts that can be enforced by scripts deployed on a blockchain, as well as some tools for analysing and simulating the execution of contracts written in the DSL.

## Learning about Marlowe and Meadow

The [Marlowe tutorials](./docs/README.md) introduce Marlowe and Meadow.

## Version 1.3, stable branch, master branch, and version 2.0

The last stable version of Marlowe can be found in the branch `stable`. This branch currently contains very small improvements with respect to version `1.3` and is the one in which the current version of Meadow is based (see Meadow section below). For the pure version `1.3` you can check the `v1.3` tag. A full description of the `1.3` version was presented at ISoLA 2018, and the paper is available [here](https://iohk.io/research/papers/#2WHKDRA8).   

The `master` branch contains the latest developments of Marlowe. Because of this, the Haskell semantics, the Coq formalisation, and the Meadow implementation, may be out of sync with each other in this branch, but they contain the latest functionality. The latest version of Marlowe `v2.0` is inside the folder `semantics-2.0`; the `src` folder contains the last `1.x` version.

## Meadow and Meadow in the cloud

Meadow is a browser-based demo prototype that supports graphical editing of smart-contracts (thanks to the Blockly library) and block by block simulation of their execution (translated from the semantics thanks to the Haste compiler).

Meadow is available at: https://input-output-hk.github.io/marlowe/ and a video showing Meadow in Action is here: https://youtu.be/_loz70XkHM8 


Together with the last version of Marlowe (`v2.0`) we have also developed a redesigned version of Meadow called Meadow in the cloud. Meadow in the cloud can be found [here](https://prod.meadow.marlowe.iohkdev.io).

## Build on MacOS

Requirements: Homebrew, Haskell Stack 1.6 or later.

Install Haskell Stack if you haven't already

    $ brew install haskell-stack

    $ brew install glpk
    $ stack setup
    $ stack build

