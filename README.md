<p align="center">
  <img width="266" height="185" src="docs/pix/logo.png">
</p>

# Marlowe

This repository contains Marlowe, a domain-specific language (DSL) for describing financial smart contracts that can be enforced by scripts deployed on a blockchain, as well as some tools for analysing and simulating the execution of contracts written in the DSL.

## Version 1.3, stable branch, and master branch

The last stable version of Marlowe can be found in the branch `stable`. This branch currenty contains very small improvements with respect to version `1.3` and is the one in which the current version of Meadow is based (see Meadow section below). For the pure version `1.3` you can check the `v1.3` tag. A full description of the `1.3` version was presented at ISoLA 2018, and the paper is available [here](https://iohk.io/research/papers/#2WHKDRA8).   

The `master` branch contains the latest developments of Marlowe. Because of this, the Haskell semantics, the Coq formalisation, and the Meadow implementation, may be out of sync with each other in this branch, but they contain the latest functionality.

## Main files

The following are some of the main files included in this repository:

- `src/Semantics.hs` —  contains the small-step semantics of DSL (`stepBlock` function), together with a simple driver (`driver` function).
- `src/ContractFormatter.hs` — contains the implementation of a formatter for scdsl code.
- `src/SmartInputs.hs` — contains code that calculates possible inputs for a
 given input, state, contract, and observables value.
- `src/DepositIncentive.hs` —  contains an example contract for incentivising saving.
- `src/CrowdFunding.hs` —  contains an example contract for crowd-funding limited to 4 participants.
- `src/Escrow.hs` —  contains an example contract for an escrow payment.

## Meadow

Meadow is a browser-based demo prototype that supports graphical editing of smart-contracts (thanks to the Blockly library) and block by block simulation of their execution (translated from the semantics thanks to the Haste compiler).

Meadow is available at: https://input-output-hk.github.io/marlowe/ and a video showing Meadow in Action is here: https://youtu.be/_loz70XkHM8 

The sources for Meadow are available in the `meadow` folder.

## Build on MacOS

Requirements: Homebrew, Haskell Stack 1.6 or later.

Install Haskell Stack if you haven't already

    $ brew install haskell-stack

    $ brew install glpk
    $ stack setup
    $ stack build

