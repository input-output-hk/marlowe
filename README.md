# Smart contract DSL prototype (scdsl)

This repository contains a preliminary design of a DSL for describing smart-contracts that can be enforced by scripts deployed on a cryptocurrency's blockchain, and some tools for analysing and simulating the execution of contracts written in the DSL.

- `Semantics.hs` —  contains the small-step semantics of DSL (`fullStep` function), together with a simple driver (`driver` function).
- `DepositIncentive.hs` —  contains an example contract for incentivising saving.
- `Analysis.hs` —  contains functions for analysing all the possible outcomes of running the DSL (`analysis` function).

## Interactive demo

A browser-based demo prototype is available that supports graphical editing of smart-contracts (thanks to the Blockly library) and block by block simulation of their execution (translated from the semantics thanks to the Haste compiler).

The demo is available at: https://input-output-hk.github.io/scdsl/

The sources are available in the blockly folder.

## Analysis

For analysing all the possible outcomes of a contract we run the function `analysis`. The number of possible outcomes can be large so we can filter them using some criteria. For example, for executing analysis on the rock-paper-scissors contract we may run:

```
Prelude> :l Analysis.hs DepositIncentive.hs
*Analysis> get_unique_action_seqs $ only_stable $ only_null $ analysis DepositIncentive.depositIncentive
```

This will produce a list of possible unique outcomes (represented as lists of actions) on which the contract is consumed completely (it is reduced to NULL), and which are stable (waiting for longer would not trigger any actions).

## Disclaimer

The analysis tool and simulator are in early development stage, correctness is not guaranteed, use at your own risk.
