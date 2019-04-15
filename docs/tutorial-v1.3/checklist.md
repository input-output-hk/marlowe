# Converting Marlowe contracts from v1.3 to v2.0

The [overview](./differences.md) describes the differences between Marlowe 2.0 and Marlowe 1.3; here that information is presented as a checklist for converting contracts between v1.3 and v2.0.

## Checklist

1. `CommitCash` expressions in `Contract`:

   Rename the constructor to `Commit`.

   An _action id_ field needs to be added as the first field of the constructor. As long as it is unique within the contract, the particular value is not relevant to the behaviour of the contract, but is used in constructing inputs, e.g. in Meadow.

   The amount of money to be comitted must be converted from type `Money` to type `Value`, see item 3.

2. `Pay` constructs in `Contract`:

   An _action id_ field needs to replace the payment id as the first field of the constructor. Note that this must be unique within the contract.

   The `Person` making the contract is no longer a field; this is replaced by the `IdCommit` of the commitment from which the payment is to be made.

   Payments originally had a single continuation `Contract`, irrespective of whether or not the construct had timed out. This is now distinguished, and so the original continuation should be duplicated.

   The amount of money to be paid must be converted from type `Money` to type `Value`, see item 3.

3. Expressions of type `Money` should be renamed to their corresponding expressions of type `Value`:

   <table>
      <tr><th>Marlowe 1.3</th><th>Marlowe 2.0</th></tr>
      <tr><td>AvailableMoney</td><td>Committed</td></tr>
      <tr><td>AddMoney</td><td>AddValue</td></tr>
      <tr><td>ConstMoney</td><td>Constant</td></tr>
      <tr><td>MoneyFromChoice</td><td>ValueFromChoice</td></tr>
   </table>

4. `Redeem` expressions in `Contract`:

   The `Redeem` constructor has been removed, and it should be replaced by a `Pay` constructor. This will be a payment from the commitment to the person who made the commitment initially.
   
   More details of how to construct payments in v2.0 are given above, but note that the extra information required will include an action id, a timeout, and a continuation to use if the timeout is exceeded.

5. Choices:

   Identifiers for choices now include the choice and the participant as part of the identifier as described in the [overview document](./differences.md). 
   This affects `Observation`s and `Money` expressions that depend on choices:
    * `PersonChoseThis idCh per c` becomes `ChoseThis (idCh, per) c`
    * `PersonChoseSomething idCh per c` becomes `ChoseSomething (idCh, per) c`
    * `MoneyFromChoice idCh per val` becomes `ValueFromChoice (idCh, per) val`

## Where to go to find out more

- The discussions about _embedded Marlowe_ in the tutorials: [v1.3](embedded-marlowe.md), [v2.0](../tutorial-v2.0/embedded-marlowe.md), give a complete example of a contract in both versions of the language.

- Here are tutorials on [Marlowe v1.3](./README.md) and [Marlowe v2.0](../tutorial-v2.0/README.md), and [Meadow in the cloud](https://prod.meadow.marlowe.iohkdev.io).

- The semantics of Marlowe 2.0 can be found [here](https://github.com/input-output-hk/marlowe/blob/v1.3/src/Semantics.hs).

