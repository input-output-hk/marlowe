# The semantics of Marlowe 2.0

This tutorial gives a high-level formal semantics of Marlowe 2.0 by describing the types of inputs supported, and by showing the Haskell code for the main functions that constituite the semantics.

In general, participants of a Marlowe contract can communicate with the contract by issuing transactions. From the point of view of Marlowe's semantics, a transaction consists basically of a list of inputs that may be signed by one or more participants. In the semantics, we represent a transaction as a list of inputs together with a set of integer numbers (the set of integer numbers represents the set of participants that signed the transaction).

As we mentioned in the previous tutorial, inputs can have one out of four types: `Commit`, `Pay`, `Choice`, and `Oracle`. From these four types, `Commit` and `Pay` are considered actions and have typically associated the transference of some money between the participant and the contract. `Choice` and `Oracle` are used to provide information from the external world to the contract.

## The `applyTransaction` function

The effect that a transaction has in a Marlowe contract is modelled by the top-level function `applyTransaction`, which takes the transaction to process and the current state of the contract (including the internal state, the remaining contract, and the amount of funds remaining in the contract), and it returns the new state of the contract together with the amount of money that each participant is suppoused to transfer to or from the contract as part of the transaction.

<p align="center">
  <img width="100%" src="pix/applyTransaction.svg">
</p>

In Haskell the type of the `applyTransaction` function remains as follows:

```haskell
applyTransaction :: [AnyInput] -> S.Set Person -> BlockNumber -> State -> Contract -> Integer
                    -> MApplicationResult (Integer, TransactionOutcomes, State, Contract)
```

In turn, the `applyTransaction` function calls three fundamental auxiliar functions in the semantics: `reduce`, `fetchPrimitive`, and `eval`. The `reduce` function is applied before and after every input, `fetchPrimitve` is applied only for inputs that are actions (i.e: `Commit` and `Pay` inputs), and `eval` is applied to the result of `fetchPrimitive` whenever appropriate.

In addition to these three functions, there are three additional functions that are applied in every transaction. Before processing the inputs, the function `expireCommits` is applied, and after processing the inputs the functions `redeemMoney` and `simplify` are applied.

<p align="center">
  <img width="500px" src="pix/flowchart.svg">
</p>

