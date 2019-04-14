# Using Marlowe

This tutorial shows you how to use Marlowe from within Haskell, and in particular shows how to exercise a contract using the semantics given in the [earlier tutorial](./marlowe-semantics.md).

## Marlowe in Haskell

This tutorial works in `v2.0` of Marlowe which can be found under semantics-2.0 in the `master` branch of the repository:
```bash
git clone https://github.com/input-output-hk/marlowe.git
cd semantics-2.0
```

## Stepping through contracts

As we saw in the [semantics for Marlowe](./marlowe-semantics.md) the semantics of a single transaction are defined by the function `applyTransaction` of type:
 ```haskell
applyTransaction :: [AnyInput] -> S.Set Person -> BlockNumber -> State -> Contract -> Integer
                    -> MApplicationResult (Integer, TransactionOutcomes, State, Contract)
```

As illustrated by the diagram:

<p align="center">
 <img width="100%" src="pix/applyTransaction.svg">
</p>

We can use the facilities of `ghci` to step through a contract one transaction at a time, and, here, we will do that with the embedded escrow contract contained in [`Escrow.hs`](https://github.com/input-output-hk/marlowe/blob/master/semantics-2.0/examples/pure/Escrow.hs).

To single step, you can work in `ghci` like this, using the facility to make local bindings:

```haskell
*Build Data.Set> let (MSuccessfullyApplied (am1, to1, st1, c1) r1) = applyTransaction inputList1 (Data.Set.fromList sigList1) blockNum1 emptyState initialContract 0
*Build Data.Set> let (MSuccessfullyApplied (am2, to2, st2, c2) r2) = applyTransaction inputList2 (Data.Set.fromList sigList2) blockNum2 st1 c1 am1
*Build Data.Set> let (MSuccessfullyApplied (am3, to3, st3, c3) r3) = applyTransaction inputList3 (Data.Set.fromList sigList3) blockNum3 st2 c2 am2
*Build Data.Set> ...
```

Where `inputList`s are lists of inputs that may include any number of inputs depending on the context, and `sigList`s are lists of participant identifiers that represent the signatories of the transaction and there may also be any number of them.

And we can then explore the values produced. Note, however, that the local bindings are lost each time a `:load` or `:l` command is performed.

An alternative way of doing this is to add these definitions to a working file, e.g. `Build.hs`, where these definitions will be preserved. Indeed, it would be very sensible to include some of the definitions used above in such a file.

The earlier description of the [semantics](./marlowe-semantics.md) concentrated on the high-level steps taken, and did not cover the constituent types in much detail. These are all defined in [`Semantics.hs`](https://github.com/input-output-hk/marlowe/blob/master/semantics-2.0/Semantics.hs)

## States and Inputs

**TODO**

## Back to single stepping

**TODO**

## There must be an easier way!

Yes, there is! 
       
We look next at how we can build a tool, Meadow, that will capitalise on the fact that we are working in a DSL to _automate_ picking the right inputs and allow users to interact with contracts.


### [Prev](./embedded-marlowe.md) [Up](./README.md) [Next](./meadow-overview.md)
