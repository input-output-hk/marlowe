# Converting Marlowe contracts from v1.3 to v2.0

The [overview](./differences.md) describes the differences between Marlowe 2.0 and Marlowe 1.3; here that information is presented as a checklist for converting contracts between v1.3 and v2.0.

## Checklist

1. `CommitCash` expressions in `Contract`:

   Rename the constructor to `Commit`.

   An _action id_ field needs to be added as the first field of the constructor. As long as it is unique within the contract, the particular value is not relevant to the behaviour of the contract, but is used in constructing inputs, e.g. in Meadow.

   The constructor `ConstMoney` of type `Money` should be replaced by  `Constant` of type `Value`.

1. `Pay` constructs in `Contract`:

   An _action id_ field needs to replace the payment id as the first field of the constructor. Note that this must be unique within the contract.

   The `Person` making the contract is no longer a field; this is replaced by the `IdCommit` of the commitment from which the payment is to be made.

   Payments originally had a single continuation `Contract`, irrespective of whether or not the construct had timed out. This is now distinguished, and so the original continuation should be duplicated.

   The constructor `ConstMoney` and `AvailableMoney`  of type `Money` should be replaced by `Constant` and `Committed` of type `Value`.

1. `Redeem` expressions in `Contract`:

   The `Redeem` constructor has been removed, and it should be replaced by a `Pay` constructor. This will be a payment from the commitment to the person who made the commitment initially.
   
   More details of how to construct payments in v2.0 are given in the previous item, but note that the extra information required will include an action id, a timeout, and a continuation to use if the timeout is exceeded.

1. `When` and `Choice` contracts.

   These are not changed at the top level, but `Observation` values within them are changed. In particular, choices are structured in a different way as described in the [overview document](./differences.md). 

   For example, the construct  
   `PersonChoseThis … per c`  
   becomes  
   `ChoseThis (idCH, per) c`  
   where `idCH` identifies the choice.

## Where to go to find out more

- Here are tutorials on [Marlowe v1.3](./README.md) and [Marlowe v2.0](../tutorial-v2.0/README.md), and [Meadow in the cloud](https://prod.meadow.marlowe.iohkdev.io).

- The semantics of Marlowe 2.0 can be found [here](https://github.com/input-output-hk/marlowe/blob/v1.3/src/Semantics.hs).

