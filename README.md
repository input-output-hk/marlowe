# Smart contract DSL prototype (scdsl)

This repository contains a preliminary design of a DSL for describing smart-contracts that can be enforced by scripts deployed on a cryptocurrency's blockchain, and some tools for analysing and simulating the execution of contracts written in the DSL.

- `Semantics.hs` —  contains the small-step semantics of DSL (`full_step` function), together with a simple driver (`driver` function).
- `RPS.hs` —  contains an implementation of the game rock-paper-scissors in the DSL (`rps` function).
- `Interactive.hs` —  contains a simple interactive prompt interface for simulating smart contracts written in the DSL (`interact_contract` function) and functions for pretty-printing contracts (`prettyprint_con` function).
- `Analysis.hs` —  contains functions for analysing all the possible outcomes of running the DSL (`analysis` function).

## Interactive mode

For example, for simulating the execution of the rock-paper-scissors game using the interactive prompt the following expression can be evaluated from the `ghci`:

```
Prelude> :l Interactive.hs RPS.hs
*Interactive> interact_contract RPS.rps
```

The program will then show the remaining contract at each point and offer a series of possible commands that can be given to the prompt.

## Analysis

For analysing all the possible outcomes of a contract we run the function `analysis`. The number of possible outcomes can be large so we can filter them using some criteria. For example, for executing analysis on the rock-paper-scissors contract we may run:

```
Prelude> :l Analysis.hs RPS.hs
*Analysis> get_unique_action_seqs $ only_stable $ only_null $ analysis RPS.rps
```

This will produce a list of possible unique outcomes (represented as lists of actions) on which the contract is consumed completely (it is reduced to NULL), and which are stable (waiting for longer would not trigger any actions).

## Disclaimer

The analysis tool and simulator are in early development stage, correctness is not guaranteed, use at your own risk.
