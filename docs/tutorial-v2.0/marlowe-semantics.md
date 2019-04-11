# The semantics of Marlowe 2.0

This tutorial gives a high-level formal semantics of Marlowe 2.0 by describing the types of inputs supported, and the main semantic functions.

In general, participants in a Marlowe contract communicate with the contract by issuing _transactions_. At each block, a sequence of zero or more transactions can be processed – in sequence – by a contract.

From the point of view of the semantics, a transaction consists of a list of inputs, and the whole transaction may be _signed_ by one or more participants. Concretely, we represent a transaction as a list of `AnyInput`s together with a set of integers representing the set of signatories.

As we mentioned in [the previous tutorial](./marlowe-data.md), inputs can have one out of four kinds: `Commit`, `Pay`, `Choice`, and `Oracle`. Of these, `Commit` and `Pay` are considered to be _actions_ and are typically associated with the transfer of money between a participant and the contract. `Choice` and `Oracle` are used to provide information from the external world to the contract.




## The `applyTransaction` function

The effect of executing a transaction in a Marlowe contract is modelled by the top-level function `applyTransaction`. This takes the transaction to process and the current state of the contract (including the internal state, the remaining contract, and the amount of funds remaining in the contract), and it returns the new state of the contract together with the amount of money that each participant is supposed to transfer to or from the contract as part of the transaction.

<p align="center">
 <img width="100%" src="pix/applyTransaction.svg">
</p>

The `applyTransaction` function has the following Haskell type:

```haskell
applyTransaction :: [AnyInput] -> S.Set Person -> BlockNumber -> State -> Contract -> Integer
                    -> MApplicationResult (Integer, TransactionOutcomes, State, Contract)
```

In turn, the `applyTransaction` function calls three principal auxiliary functions: `reduce`, `fetchPrimitive`, and `eval`.

- The `reduce` function is applied before and after every input, 
- `fetchPrimitive` is applied only for inputs that are actions (i.e: `Commit` and `Pay` inputs), and 
- `eval` is applied to the result of `fetchPrimitive` whenever appropriate.

In addition to these three functions, there are three additional functions that are applied in every transaction. Before processing the inputs, the function `expireCommits` is applied, and after processing the inputs the functions `redeemMoney` and `simplify` are applied.

<p align="center">
  <img width="500px" src="pix/flowchart.svg">
</p>

