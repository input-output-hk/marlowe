# A first example

This tutorial introduces a simple financial contract in pseudocode, before explaining how it is modified to work in Marlowe, giving the first example of a Marlowe contract.

## A simple escrow contract

![Escrow](./pix/escrow.png)


Suppose that `alice` wants to buy a cat from `bob`, but neither of them trusts the other. Fortunately, they have a mutual friend `carol` whom they both trust to be neutral (but not enough to give her the money and act as an intermediary). They therefore agree on the following contract, written using simple functional pseudocode. This kind of contract is a simple example of _escrow_.
```haskell
(When (Or (two_chose alice bob carol refund)
          (two_chose alice bob carol pay))
      (Choice (two_chose alice bob carol pay)
              (Pay alice bob AvailableMoney)
              redeem_original))
```              
The contract is described using the _constructors_ of a Haskell data type. The outermost constructor `When` has two arguments: the first is an _observation_ and the second is another contract. The intended meaning of this is that _when_ the observation becomes true, the second contract is activated.

The observation here is a disjunction, which is true 
- if two of the participants (presumably `carol` the trusted intermediary, and `bob`) agree that `bob` should be paid (the `pay` contract), or 
- if two of the participants (presumably, in this case, `carol` and `alice`) agree that `alice` should be refunded (`refund`). 


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

In a similar way, because a payment cannot be performed directly by the contract, but _must be initiated by the participant_ making the payment, the `Pay` sub-contract is given a timeout (of `100`) for the payment to be claimed. If the timeout happens, then the contract  `redeem_original` will be performed. The contract also _identifies_ the payment with `iP1` and refers to a commitment through its identifier, `iCC1`:

```haskell
(When (Or (two_chose alice bob carol refund)
          (two_chose alice bob carol pay))
      90                 
      (Choice (two_chose alice bob carol pay)
              (Pay iP1 alice bob (AvailableMoney iCC1) 100 redeem_original) -- ADDED
              redeem_original))
      redeem_original     
```  



In a similar way, the `Pay` sub-contract is given a timeout and a contract to perform on timeout, which is again `redeem_original`.

Finally, we should look at how cash is committed as the first step of the contract.

```haskell
CommitCash iCC1 alice (ConstMoney 450) 10 100  -- ADDED
                    (When (OrObs (two_chose alice bob carol refund)
                                 (two_chose alice bob carol pay))
                          90
                          (Choice (two_chose alice bob carol pay)
                                  (Pay iP1 alice bob (AvailableMoney iCC1) 100
                                       redeem_original)
                                  redeem_original)
                          redeem_original)
           Null                               -- ADDED
```
The commitment requested from `alice` is given an identifier, `iCC1`. The cash value (`450`) and timeout (`100`) on the commitment are also specified. Moreover, a _timeout on making the commitment_, `10`, is also specified as part of the contract, too, as well as a contract to be followed if the commitment is not forthcoming: that is  `Null` in this case.


> __Exercise__
>  
> Comment on the choice of timeout values, and look at alternatives. For example,  what would happen if the timeout on the `When` (`90`) were to be replaced by `110`? Is it sensible to have the same timeout (`100`) on both the commitment and the payment? If not, what choice would you make?


Why have we included identifiers in commitments and payments, in this case `iCC1` and `iP1`? The identifier is used to identify the commit in a `RedeemCC` or in a `Both` construct to identify a payment or commitment. In the former case to clarify what is being redeemed, and in the latter to distinguish between constructs in the two branches of a `Both`. For a contract to be properly constructed, identifiers need to be unique: i.e they need to identify a single construct only.

This example has shown many of the ingredients of the Marlowe contract language; in the next tutorial we will present the complete language. 

Notes
- While identifiers need to be provided manually in the example here, these could be generated by users’ wallets in a version of Marlowe deployed on a blockchain. We will say more about this in [ADD LINK]().
- Many of the items used here, including, for example `alice` and `two_chose`, and defined using the embedded DSL, which is discussed in more detail when we look at [embedded Marlowe](./embedded-marlowe.md).

## Where to go to find out more

- [Composing contracts: an adventure in financial engineering](https://www.microsoft.com/en-us/research/publication/composing-contracts-an-adventure-in-financial-engineering/)
- [Certified symbolic management of financial multi-party contracts](https://dl.acm.org/citation.cfm?id=2784747)


### [Prev](./introducing-marlowe.md) [Up](./README.md) [Next](./marlowe-data.md)