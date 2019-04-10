# The semantics of Marlowe 2.0

This tutorial gives a high-level formal semantics of Marlowe 2.0 by describing the types of inputs supported, and by showing the Haskell code for the main functions that constituite the semantics.

In general, participants of a Marlowe contract can communicate with the contract by issuing transactions. From the point of view of the Marlowe's semantics, a transaction consists basically of a list of inputs that may be signed by one or more participants.

Inputs can have one out of four types: `Commit`, `Pay`, `Choice`, and `Oracle`. From these four types, `Commit` and `Pay` are considered actions and have typically associated the transference of some money between the participant and the contract. `Choice` and `Oracle` are used to provide information from the external world to the contract.

Transaction inputs are processed mainly by three fundamental functions in the semantics: `reduce`, `fetchPrimitive`, and `eval`. The `reduce` function is applied before and after every input, `fetchPrimitve` is applied only for inputs that are actions (i.e: `Commit` and `Pay` inputs), and `eval` is applied to the result of `fetchPrimitive` whenever appropriate.

In addition to these three functions, there three additional functions that are applied in every transaction. Before processing the inputs, the function `expireCommits` is applied, and after processing the inputs the functions `redeemMoney` and `simplify` are applied.


