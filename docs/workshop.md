# Marlowe workshop

## Getting started with Marlowe

Using the BLOCKLY tab, try building these contracts

1. Make a payment of 2 Lovelace from Alice to Bob, from Alice's account.
1. Modify contract 1 to ask for a deposit of money from Alice into her account before the payment is made.
1. Modify contract 2 to ask for a decision from Carol. Carol should choose 0 or 1: if she chooses 1, the payment from Alice's account is split between Alice and Bob; if zero, it all goes to Bob.
1. Analyse the three contracts that you have written. Try modifying the contracts so that ones that didn't pass now do, and vice versa. 

## “Bulgarian escrow”: modifying the escrow contract

Modify the Haskell escrow contract to a “Bulgarian” variant in which Bob has to make a deposit in advance. This is returned to him if gives up the cat, but goes to Alice if he does not.

## Challenge: utility contract

The challenge is to write a Marlowe contract that models payments for a utility, such as a mobile phone.

The contract models the fact that you make regular payments to the company, every 30 slots. These payments are specified by the company, and you have 10 slots in which to pay. To start with, model the situation where the payment is 40 Ada each month.

At the start of the contract you make a deposit, say 150 Lovelace, and during the year, if you do not pay on time the company keeps the full deposit. If you have paid regularly, at the end of the contract  the deposit is paid back to you.

### Blockly and the Marlowe Playground

If you are writing the contract in Blockly, model a contract that includes two cycles of 30 slots.

If you are writing the contract in Haskell using the Marlowe Playground, write a version that is parameterised over the number of cycles.

### Variants

You can try to add these variants, either one at a time, or in combination.

- Model the situation where the company can specify (using a choice `Action`) how much to pay at the time of payment rather than having it fixed in advance in the contract.
- You can cancel the subscription giving 30 slots notice; on doing this you can recover half the deposit.
- The company can increase the fixed fee by a given amount once only,  giving 20 slots notice. If this is done, then you can withdraw from the contract without losing your deposit.

### Analysis

For each contract that you write, does your contract pass the analysis? If not, how could you modify it so that it passes?

## Links

- The [Marlowe Playground](https://alpha.marlowe.iohkdev.io).

- The [Marlowe github repo](https://github.com/input-output-hk/marlowe).


