# Marlowe hackathon challenge: utility contract

The challenge is to write a Marlowe contract that models payments for a utility, such as a mobile phone.

The contract models the fact that you make regular payments to the company, every 3 hours. These payments are specified by the company, and you have 1 hour in which to pay. To start with, model the situation where the payment is 40 Ada each month.

At the start of the contract you make a deposit, say 150 Ada, and during the year, if you do not pay on time the company keeps the full deposit. If you have paid regularly, at the end of the contract  the deposit is paid back to you.

## Blockly and the Marlowe Playground

If you are writing the contract in Blockly, model a contract that includes two cycles of 3 hours.

If you are writing the contract in Haskell using the Marlowe Playground, write a version that is parameterised over the number of cycles.

## Variants

You can try to add these variants, either one at a time, or in combination.

- Model the situation where the company can specify (using a `Choice`) how much to pay at the time of payment rather than having it fixed in advance in the contract.
- You can cancel the subscription giving 3 hours notice; on doing this you can recover half the deposit.
- The company can increase the fixed fee by a given amount once only,  giving 2 hours notice. If this is done, then you can withdraw from the contract without losing your deposit.


