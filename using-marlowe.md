# Using Marlowe

This tutorial shows you how to use Marlowe from within Haskell, and in particular shows how to exercise a contract using
the semantics given in the (**ToDo: Broken link**)[earlier tutorial](./marlowe-semantics.md).

## Marlowe in Haskell

This tutorial works in `v3.0` of Marlowe which can be found under semantics-3.0 in the `master` branch of the repository:
```bash
git clone https://github.com/input-output-hk/marlowe.git
cd semantics-3.0
```

## Stepping through contracts

As we saw in the (**ToDo: Broken link**)[semantics for Marlowe](./marlowe-semantics.md) the semantics of a single transaction
are defined by the function `processTransaction` of type:

```haskell
processTransaction :: Transaction -> State -> Contract -> ProcessResult
```

Where `Transaction` is defined as:

```haskell
data Transaction = Transaction { interval :: TimeInterval
                               , inputs :: [Input] }
```

Where `interval` represents the time interval in which the transaction is added to the blockchain. And `inputs` is a list
of the actions issued by participants as part of the transaction.

`ProcessResult` is defined as:

```haskell
data ProcessResult = Processed [ProcessWarning]
                               [ProcessEffect]
                               TransactionSignatures
                               TransactionOutcomes
                               State
                               Contract
                   | ProcessError ProcessError
```

If the transaction is valid given the current `State` and `Contract`, the `ProcessResult` includes a list of warnings,
a list of effects (currently payments), a list of participants that must have signed the transaction, and a list of the
monetary outcomes per participant, as well as the new `State` and `Contract`.

As illustrated by the diagram:

<p align="center">
 (<b>ToDo: diagram</b>)
</p>

We can use the facilities of `ghci` to step through a contract one transaction at a time, and, here, we will do that with
the embedded Zero Coupon Bond Guaranteed contract contained
in [`ZCBG.hs`](https://github.com/input-output-hk/marlowe/blob/master/semantics-3.0/ZCBG.hs).

To single step, you can work in `ghci` like this, using the facility to make local bindings:

```haskell
*ZCBG Semantics> Processed warns1 effs1 sigs1 outs1 st1 c1 = processTransaction (Transaction (li1, hi1) inps1) st c
*ZCBG Semantics> Processed warns2 effs2 sigs2 outs2 st2 c2 = processTransaction (Transaction (li2, hi2) inps2) st1 c1
*ZCBG Semantics> Processed warns3 effs3 sigs3 outs3 st3 c3 = processTransaction (Transaction (li3, hi3) inps3) st2 c2
*ZCBG Semantics> ...
```

Where `inps`s are lists of inputs that may include any number of inputs depending on the context, the numbers `li`s and
`hi`s denote the interval in which the slot number in which each transaction is accepted in the blockchain.

We can then explore the values produced. Note, however, that the local bindings are lost each time a `:load` or `:l` command
is performed.

An alternative way of doing this is to add these definitions to a working file, e.g. `Build.hs`, where these definitions will
be preserved. Indeed, it would be very sensible to include some of the definitions used above in such a file.

The earlier description of the (**ToDo: Broken link**)[semantics](./marlowe-semantics.md) concentrated on the high-level
steps taken, and did not cover the constituent types in much detail. These are all defined in
(**ToDo: Broken link**)[`Semantics.hs`](https://github.com/input-output-hk/marlowe/blob/master/semantics-2.0/Semantics.hs)

## State

The `State` of a Marlowe contract keeps track of the amount of money in each `account`, the values of `choice`s made by
users, and the highest known lower bound for the most recent slot number.

```haskell
data State = State { account :: Map AccountId Money
                   , choice :: Map ChoiceId ChosenNum
                   , minTime :: POSIXTime }
```

## Inputs

For the contract to progress, it needs to be presented with inputs, as represented by the `Input` type, which has three
subtypes:
 * `IDeposit` represents a deposit of money made by a participant.
 * `IChoice` reperesents the choice of an `Integer` value by a participant.
 * `INotify` is used by a participant to "trigger" or "notify" the contract that an observation has become `True`.

```haskell
data Input = IDeposit AccountId Party Money
           | IChoice ChoiceId ChosenNum
           | INotify
```

The list of `Input`s may be empty whenever we want to notify the contract that a timeout has occurred.

## Back to single stepping

To single step through the Zero Coupon Bond Guaranteed contract we construct three transaction to represent
three deposits, and one transaction to notify the contract about a timeout. One for the guarantor (for the
amount of the notional), one for the investor (for the amount of the notional minus the discount),
and later a repayment by the issuer (for the amount of the notional).

Together these represent the successful execution of the Zero Coupon Bond Guaranteed contract, and we can observe
it will issue a series of payments in response, by looking at `effs` and at `outs`.

```haskell
*ZCBG Semantics> let c = zeroCouponBondGuaranteed 1 2 3 1000 200 10 20
*ZCBG Semantics> let st = emptyState 0
*ZCBG Semantics> Processed warns1 effs1 sigs1 outs1 st1 c1 = processTransaction (Transaction (0, 9) [IDeposit (AccountId 1 3) 3 1000]) st c
*ZCBG Semantics> Processed warns2 effs2 sigs2 outs2 st2 c2 = processTransaction (Transaction (3, 9) [IDeposit (AccountId 2 2) 2 800]) st1 c1
*ZCBG Semantics> Processed warns3 effs3 sigs3 outs3 st3 c3 = processTransaction (Transaction (10, 12) []) st2 c2
*ZCBG Semantics> Processed warns4 effs4 sigs4 outs4 st4 c4 = processTransaction (Transaction (17, 19) [IDeposit (AccountId 2 2) 1 1000]) st3 c3
*ZCBG Semantics> ...
```

Why is single stepping useful? It is the equivalent of debugging, and we are able to see the internal state of the contract
at each stage, the contract continuation, i.e. what remains to be executed, and the actions produced at each step.

> __Exercise__
>  
> Explore some other ways of engaging with the contract
> - What happens when the guarantor does not make the deposit on time?
> - What happens when the issuer does not return the money?
> - What happens when we pass an interval that includes times both before and after a timeout?

## There must be an easier way!

Yes, there is! 
       
We look next at how we can build a tool, the Marlowe Playground, that will capitalise on the fact that we are working in a
DSL to _automate_ picking the right inputs and allow users to interact with contracts.


### (**ToDo: Broken link**)[Prev](./embedded-marlowe.md) (**ToDo: Broken link**)[Up](./README.md) (**ToDo: Broken link**)[Next](./playground-overview.md)
