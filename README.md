# Smart contract DSL prototype (scdsl)

This repository contains a preliminary design of a DSL for describing smart-contracts that can be enforced by scripts deployed on a cryptocurrency's blockchain, and some tools for analysing and simulating the execution of contracts written in the DSL.

- `src/Semantics.hs` —  contains the small-step semantics of DSL (`fullStep` function), together with a simple driver (`driver` function).
- `src/ContractFormatter.hs` — contains the implementation of a formatter for scdsl code.
- `src/SmartInputs.hs` — contains code that calculates possible inputs for a
 given input, state, contract, and observables value.
- `src/DepositIncentive.hs` —  contains an example contract for incentivising saving.
- `src/CrowdFunding.hs` —  contains an example contract for crowd-funding limited to 4 participants.
- `src/Escrow.hs` —  contains an example contract for an escrow payment.

## Interactive demo

A browser-based demo prototype is available that supports graphical editing of smart-contracts (thanks to the Blockly library) and block by block simulation of their execution (translated from the semantics thanks to the Haste compiler).

The demo is available at: https://input-output-hk.github.io/scdsl/

The sources for the demo are available in the blockly folder.
