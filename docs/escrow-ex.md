# A first example

This tutorial examines how a Haskell data type can be used to describe a contract, first in the abstract, and then in the blockchain context using Marlowe.

## A simple escrow contract

![Escrow](./pix/escrow.png)


Suppose that `alice` wants to buy a cat from `bob`, but neither of them trusts the other. Fortunately, they have a mutual friend `carol` whom they both trust. They therefore agree on the following contract, written using simple functional pseudocode. This kind of contract is a simple example of _escrow_.
```haskell
(When (Or (two_chose alice bob carol refund)
          (two_chose alice bob carol pay))
      (Choice (two_chose alice bob carol pay)
              (Pay alice bob AvailableMoney)
              redeem_original))
```              
The contract is described using the _constructors_ of a Haskell data type. The outermost constructor `When` has two arguments: the first is an _observation_ and the second is another contract. The intended meaning of this is that _when_ the observation becomes true, the second contract is executed.

The observation here is a disjunction: it is true if two of the participants (presumably `carol` the trusted intermediary, and `bob`) agree that `bob` should be paid, or if two (in this case `carol` and `alice`) agree that `alice` should be refunded.

The second contract is itself a `Choice` depending on whether or not there has been agreement to pay `bob`. If that is indeed the case, then the payment is offered to `bob`; if not, then a refund is offered to `alice`.

> __Exercise__
>  
> Think about executing this contract in practice. Suppose that Alice has already committed some money to the contract. What will happen if one of the participants chooses not to participate any further?
> 
> We have assumed that Alice has already committed her payment, but suppose that we want to design a contract to ensure that: what would we need to do to?

## Escrow in Marlowe

In order to make sure that the contract does indeed progress properly, we will add timeouts and commitments to is, and this will give the first example of a Marlowe contract. 

First, let us examine how to modify what we have written to take care of the case that the condition of the `When` never becomes true. We add two fields to the contract
```haskell
(When (Or (two_chose alice bob carol refund)
          (two_chose alice bob carol pay))
      90                 -- ADDED
      (Choice (two_chose alice bob carol pay)
              (Pay alice bob AvailableMoney)
              redeem_original))
      redeem_original    -- ADDED 
```  
The `90` is a _timeout_ on the time to wait for the observation to become true; if this timeout is passed, then the contract `redeem_original` is then executed, thus making sure that the money locked into the contract is not lost.

In a similar way, the `Pay` sub-contract is given a timeout and a contract to perform on timeout, which is again `redeem_original`.

## Where to go to find out more

- SPJ original paper
- Patrick Barr paper


### [Prev](./introducing-marlowe) [Up](./Tutorials.md) [Next](./marlowe-data.md)