# Marlowe 2.0: Differences with Marlowe 1.3

Marlowe 2.0 is a thorough revision of Marlowe 1.3 semantics that tries to simplify existing aspects of Marlowe, to include additional functionality, and to present an even more intuitive behaviour when executing contracts.

At the time of writing, Marlowe 2.0 is in the late stages of development but it has not reached the maturity nor the tool support of Marlowe 1.3. For these reasons, the tutorial so far has focused on Marlowe 1.3.

This tutorial aims to make it easier for users familiar with Marlowe 1.3 to transition to Marlowe 2.0, but it should not be considered as an extensive description of the differences between the two versions.

## Changes to syntax

Let us first review the changes in the syntax. The syntax of Marlowe 2.0 is very similar to that of Marlowe 1.3, but there are some important differences, and several new constructs.

### Actions and identifiers

The most important difference with Marlowe 1.3 is the separation of action constructs. In Marlowe 1.3 we had three constructs that moved money: `CommitCash`, `Pay`, and `RedeemCC`.
In Marlowe 2.0 we have two: `CommitCash` (which is now called `Commit`), and `Pay`.

There is no longer `RedeemCC` since it is equivalent to a `Pay` that has the owner of the commit as payee and the contents of the commit as value.

The actions in Marlowe 2.0 remain as follows:

```haskell
    Commit IdAction IdCommit Person Value Timeout Timeout Contract Contract
    Pay IdAction IdCommit Person Value Timeout Contract Contract
```

They are very similar to the ones in Marlowe 1.3, but we now have one identifier for the action itself `IdAction` that must be unique throughout the contract, and one identifier for the commit `IdCommit` which can be reused (even though only one `Commit` per `IdCommit` will be allowed in any given execution).

Note as well that `Pay` has now two continuations to match `Commit`, and that it now takes a source `IdCommit` instead of a payer `Person`, which makes it explicit where the money comes from.

Also note that `Commit` and `Pay` have the same type-signature except in that `Commit` has an extra `Timeout`.

### Choices and Oracles

In addition to actions, Marlowe 2.0 contracts can take two types of inputs: choices and oracles.

Choices work similarly to how they worked in Marlowe 1.3, but now we consider that a choice is identified by a pair:

```haskell
  type IdChoice = (Integer, Person)
```

So each participant can potentially respond differently to choices with the same `Integer` as first element of the pair.

Values of choices can still be observed by using the following observations:

```haskell
    ChoseThis IdChoice Choice
    ChoseSomething IdChoice
```

Or by using the following value constructor:

```haskell
    ValueFromChoice IdChoice Value
```

However, the reader should note that now all of them take a pair instead of two values. For example, to observe whether participant 1 has made a choice for choice number 3, we would write the following observation:

```haskell
  ChoseSomething (3, 1)
```

Marlowe 2.0 also includes now support for external oracles, which have their own identifier `IdOracle` and can supply values that can change at every block. Oracles can be used for representing values from the real world, such as the oil price at any given time.

Values from oracles can be observed by using the following value constructor:

```haskell
    ValueFromOracle IdOracle Value
```

## New contract constructors

Marlowe 2.0 includes some new advanced constructs for creating contracts, analogous constructs to these where already available in the late versions of Marlowe 1.x, but not in Marlowe 1.3.

### Let and Use

We have seen how it is possible to use Haskell's `let` to define and reuse expressions in embedded Marlowe. But these `let`s necessarily get expanded before the execution of the contract so, while we can use them to increase readability, we cannot use them to make the resulting Marlowe contract more concise and scalable.

Marlowe 2.0 includes one simple type of let/binding mechanism, that allows users to reuse a subcontract without expanding it until it is needed.

Marlowe's `Let` syntax is as follows:

```haskell
    Let LetLabel Contract Contract
```

The first argument `LetLabel` is the identifier for the binding, the left `Contract` is the one associated to the identifier, and the right `Contract` is the subcontract where the binding takes effect.

In that second `Contract` we can use `Use` wherever we would like to write the first `Contract`. The syntax of `Use` is as follows:

```haskell
    Use LetLabel
```

where `LetLabel` is again the identifier for the binding, which must have been defined previously by an outter `Let`, otherwise `Use` expands as `Null`.

### While

The `While` syntax is as follows:

```haskell
    While Observation Timeout Contract Contract
```

The `While` contructor works similarly to `When` but the first `Contract` is active only until the condition becomes true. After the condition becomes false, or the current block reaches the `Timeout` the `While` is reduced to the second `Contract`.

### Scale

The `Scale` syntax is a follows:

```haskell
    Scale Value Value Value Contract
```

The moment a `Scale` contract is activated, all the three `Value`s are evaluated.

Other than that, a contract wrapped by a `Scale` construct is equivalent to the inner `Contract` except in that all `Commit` and `Pay` in the `Contract` have their `Value` scaled as follows:

- If the second `Value` in Scale evaluated to zero, then `Value`s in `Commit`s and `Pay`s are taken to be the third `Value` in the `Scale`.
- Otherwise, every `Value` in a `Commit` or `Pay` is multiplied by the first `Value` in the `Scale`, and divided by the second `Value` in the `Scale` (using integer division).

## Execution and properties

In addition to the new constructs and modified syntax, Marlowe 2.0 has a slightly different execution dynamics.

In Marlowe 2.0, a transaction may include any number of inputs that may be signed by any number of participants. A transaction may in some circustances include no inputs too, in order to update the state of the contract as time passes; empty transactions need no signatures.

We have also taken a lot of care in ensuring some properties hold for all contracts. For example: in Marlowe 2.0, the `Both` construct treats both of its subcontracts equally (that is: `Both a b` is equivalent to `Both b a`); we achieve this by ensuring that each input is applied sequentially.

Another example: in Marlowe 2.0, for any given contract, there is only a finite number of inputs that the contract can accept, this reduces the chances of a DoS attack, since it is harder to find valid inputs with which to saturate a contract.

## Conclusion

We have presented some of the main differences between Marlowe 1.3 and Marlowe 2.0. Marlowe 2.0 includes many more subtle changes that are all aimed at improving the consistency, robustness, and user experience, but they are out of the scope of this tutorial.

Nevertheless, we hope that this document will help and motivate the reader to use and learn more about Marlowe 2.0.

## Where to go to find out more

The semantics of Marlowe 2.0 can be found [here](../new-semantics/Semantics.hs)

We are currently working on a new version of Meadow to include a redesigned interface and the version 2.0 of Marlowe's semantics as described in this document.

### [Prev](./marlowe-plutus.md) [Up](./Tutorials.md) [Next]()
