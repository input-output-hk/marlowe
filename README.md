# Marlowe

This repository contains the design of Marlowe, a DSL for describing smart-contracts that can be enforced by scripts deployed on a cryptocurrency's blockchain, and some tools for analysing and simulating the execution of contracts written in the DSL. The following are some of the main files included in this repository:

- `src/Semantics.hs` —  contains the small-step semantics of DSL (`stepBlock` function), together with a simple driver (`driver` function).
- `src/ContractFormatter.hs` — contains the implementation of a formatter for scdsl code.
- `src/SmartInputs.hs` — contains code that calculates possible inputs for a
 given input, state, contract, and observables value.
- `src/DepositIncentive.hs` —  contains an example contract for incentivising saving.
- `src/CrowdFunding.hs` —  contains an example contract for crowd-funding limited to 4 participants.
- `src/Escrow.hs` —  contains an example contract for an escrow payment.

A full description of the 'v1.3' version was presented at ISoLA 2018, and the paper is available [here](https://iohk.io/research/papers/#2WHKDRA8).   

## Meadow

Meadow is a browser-based demo prototype that supports graphical editing of smart-contracts (thanks to the Blockly library) and block by block simulation of their execution (translated from the semantics thanks to the Haste compiler).

Meadow is available at: https://input-output-hk.github.io/marlowe/

The sources for Meadow are available in the `meadow` folder.

## Build on MacOS

Requirements: Homebrew, Haskell Stack 1.6 or later.

Install Haskell Stack if you haven't already

    $ brew install haskell-stack

    $ brew install glpk
    $ stack setup
    $ stack build

## Stable branch

The `master` branch contains the latest developments of Marlowe, because of this, the Haskell semantics, the Coq formalisation, and the Meadow imlementation may be out of sync with each other in this branch. The `stable` branch marks a previous version of Marlowe where the different components are in sync.
