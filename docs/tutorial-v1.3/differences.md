# Marlowe 2.0: Differences with Marlowe 1.3

Marlowe 2.0 is a thorough revision of Marlowe 1.3 semantics that tries to simplify existing aspects of Marlowe, to include additional functionality, and to give more intuitive behaviour when executing contracts.

At the time of writing, Marlowe 2.0 is in the late stages of development but it has not reached the maturity nor the tool support of Marlowe 1.3. For these reasons, the tutorial so far has focused on Marlowe 1.3, but also has a version based on 2.0.

This tutorial aims to make it easier for users familiar with Marlowe 1.3 to transition to Marlowe 2.0, but it should not be considered as an exhaustive description of the differences between the two versions.

## Changes to syntax

Let us first review the changes in the syntax. The syntax of Marlowe 2.0 is similar to that of Marlowe 1.3, but there are some important differences, and several new constructs.

### Actions and identifiers

The most important difference with Marlowe 1.3 is the separation of action constructs. In Marlowe 1.3 we had three constructs that moved money: `CommitCash`, `Pay`, and `RedeemCC`.
In Marlowe 2.0 we have two: `CommitCash` (which is now called `Commit`), and `Pay`.

Marlowe 2.0 doesn't contain `RedeemCC`, since it is equivalent to a `Pay` that has the owner of the commit as payee and the contents of the commit as value.

The actions in Marlowe 2.0 remain as follows:

```haskell
Commit IdAction IdCommit Person Value Timeout Timeout Contract Contract

Pay IdAction IdCommit Person Value Timeout Contract Contract
```

They are similar to those in Marlowe 1.3, except that we have added _an identifier for the action itself_ `IdAction`, which must be unique throughout the contract. This is in addition to the identifier for the commit `IdCommit`, which can be reused within the contract, even though only one `Commit` per `IdCommit` will be allowed in any given execution.

The `IdAction` identifiers, as long as they are unique, do not affect the meaning of the contract: they are only necessary for participants to be able to specify which part of the contract they want to exercise, since there may be several possibilities (typically because of the  `Both` construct). 

It is important that `IdAction` identifiers are unique because, if a deployed contract becomes ambiguous due to replicated `IdAction` identifiers, participants of the contract will not be able to trigger any of the constructs that share an identifier.
Nevertheless, generating `IdAction` for contracts is trivial, and we intend to automate the process as we implement new tools to aid the construction and deployment of Marlowe contracts.

Note as well that `Pay` has now two continuations to match `Commit`, and that it now takes a source `IdCommit` instead of the `Person` making the payment, which makes it explicit where the money comes from. 

Also note that `Commit` and `Pay` have the same type-signature except in that `Commit` has an extra `Timeout`, representing the duration of the commitment itself.

### Choices and Oracles

In addition to actions, Marlowe 2.0 contracts can take two types of inputs: choices and oracles.

Choices work similarly to the way that they worked in Marlowe 1.3, except for the fact that we now consider that a choice is identified by a pair:

```haskell
type IdChoice = (Integer, Person)
```

This has the effect that a contract can potentially allow different participants to respond differently to a `Choice`.
Values of choices can still be observed by using the following observations:

```haskell
ChoseThis IdChoice Choice

ChoseSomething IdChoice
```

or by using the following value constructor:

```haskell
ValueFromChoice IdChoice Value
```

You should note, however, that each of them now takes a _pair_ instead of two values. For example, to observe whether participant `1` has chosen something for choice number `3`, we would write the following observation:

```haskell
ChoseSomething (3, 1)
```

Marlowe 2.0 also includes support for external _oracles_, which have their own identifier `IdOracle` and can supply values that can be different at every block. Oracles can be used for representing values from the real world, such as the oil price at any given time.
Values from oracles can be observed by using the following value constructor:

```haskell
ValueFromOracle IdOracle Value
```

## New contract constructors

Marlowe 2.0 includes some new advanced constructs for creating contracts, analogous constructs to these were already available in  later versions of Marlowe 1.x, but not in Marlowe 1.3 itself.

### `Let` and `Use`

We have seen how it is possible to use Haskell's `let` to define and reuse expressions in embedded Marlowe. But these `let`s necessarily get expanded before the execution of the contract so, while we can use them to increase readability, we cannot use them to make the resulting Marlowe contract more concise or scalable.

Marlowe 2.0 includes one simple type of let/binding mechanism, which allows users to reuse a subcontract without expanding it until it is needed. 
Marlowe's `Let` syntax is as follows:

```haskell
Let LetLabel Contract Contract
```
The first argument `LetLabel` is the identifier for the binding, the first `Contract` is that associated to the identifier, and the right `Contract` is the subcontract in which the binding takes effect.

In the second `Contract` we can use `Use` wherever we would like to write the first `Contract`. The syntax of `Use` is as follows:

```haskell
Use LetLabel
```

where `LetLabel` is again the identifier for the binding, which must have been defined by an outer `Let`, otherwise `Use` expands as `Null`.

### While

The syntax for `While` is as follows:

```haskell
While Observation Timeout Contract Contract
```

The `While` constructor works similarly to `When` but the first `Contract` is active only while the condition is true. After the condition becomes false, or the current block reaches the `Timeout`, the `While` is reduced to the second `Contract`.

### Scale

The `Scale` syntax is a follows:

```haskell
Scale Value Value Value Contract
```

When a `Scale` contract is activated, all the three `Value`s are evaluated. Other than that, a contract wrapped by a `Scale` construct is equivalent to the inner `Contract` except all `Commit` and `Pay` constructs in the `Contract` have their `Value` scaled as follows:

- If the second `Value` in Scale evaluated to zero, then `Value`s in `Commit`s and `Pay`s are taken to be the third `Value` in the `Scale`.
- Otherwise, every `Value` in a `Commit` or `Pay` is multiplied by the first `Value` in the `Scale`, and divided by the second `Value` in the `Scale` (using integer division).

## Execution and properties

In addition to the new constructs and modified syntax, Marlowe 2.0 has a slightly different execution dynamics.

In Marlowe 2.0, a transaction may include any number of inputs that may be signed by any number of participants. In some circumstances, a transaction may include no inputs, in order to update the state of the contract as time passes; empty transactions need no signatures.

We have also taken a lot of care in ensuring some properties hold for all contracts. For example: in Marlowe 2.0, the `Both` construct treats both of its subcontracts equally (that is: `Both a b` is equivalent to `Both b a`); we achieve this by ensuring that each input is applied sequentially.

Another example: in Marlowe 2.0, for any given contract, there are only a finite number of inputs that the contract can accept. This reduces the chances of a DoS attack, since it is harder to find valid inputs with which to saturate a contract.

## Conclusion

We have presented some of the main differences between Marlowe 1.3 and Marlowe 2.0. Marlowe 2.0 includes more changes that are  aimed at improving the consistency, robustness, and user experience, but they are out of the scope of this tutorial.

Nevertheless, we hope that this document will help and motivate you to use and learn more about Marlowe 2.0.

## Where to go to find out more

The semantics of Marlowe 2.0 can be found [here](https://github.com/input-output-hk/marlowe/blob/v1.3/src/Semantics.hs)

We are currently working on a new version of Meadow to include a redesigned interface and the version 2.0 of Marlowe's semantics as described in this document. **ADD LINK**

### [Prev](./marlowe-plutus.md) [Up](./README.md) [Next]()
