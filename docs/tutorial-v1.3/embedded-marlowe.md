# Embedded Marlowe

In this tutorial we go back to the escrow example, and show how we can use the _embedding_ of Marlowe in Haskell to make more readable, modular and reusable descriptions of Marlowe contracts.

## A simple escrow contract, revisited.

![Escrow](./pix/escrow.png)

Recall that we developed this Marlowe contract in our [earlier tutorial](./escrow-ex.md).


```haskell
CommitCash iCC1 alice (ConstMoney 450) 10 100  
                    (When (OrObs (two_chose alice bob carol refund)
                                 (two_chose alice bob carol pay))
                          90
                          (Choice (two_chose alice bob carol pay)
                                  (Pay iP1 alice bob (AvailableMoney iCC1) 100
                                       redeem_original)
                                  redeem_original)
                          redeem_original)
           Null                               
```
This contract makes use of the fact that Haskell allows definitions of simple abbreviations, such as
```haskell
alice  = 1
bob    = 2
carol  = 3

refund = 0
pay    = 1
```
which make our contracts more readable. Indeed Marlowe could be extended to include more meaningful ‘atomic’ data, but in our design we chose to keep such constructs to a minimum. We can also give more meaningful abbreviations for contracts and identifiers:
```haskell
redeem_original :: Contract
redeem_original = RedeemCC iCC1 Null

iCC1 :: IdentCC
iCC1 = IdentCC 1

iP1 :: IdentPay
iP1 = IdentPay 1
```
As well as defining constants, it is possible to define simple functions too, including 
```haskell
chose :: Int -> ConcreteChoice -> Observation

chose per c = 
        PersonChoseThis (IdentChoice per) per c
```
which labels a choice by person `per` (an `Int`) by an _identifier_ containing that same value, since we have used this convention in writing this particular contract to avoid having to be explicit about identifiers. (Of course, in other situations we will need to be more careful about how we use identifiers).

Given this definition we can give a description of the observation of one person (at least) choosing a particular option
```haskell
one_chose :: Person -> Person -> ConcreteChoice -> Observation

one_chose per per' val = 
        (OrObs (chose per val) (chose per' val)) 
 ```
 and using that describe the choice being made by two out of three:
 ```haskell                                 
two_chose :: Person -> Person -> Person -> ConcreteChoice -> Observation

two_chose p1 p2 p3 c =
        OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))
              (AndObs (chose p2 c) (chose p3 c))
```
Given all these definitions, we are able to write the contract at the start of this section in a way that makes its intention clear. Writing in “pure” Marlowe, or by expanding out these definitions, we would have this contract instead:
```haskell
 CommitCash (IdentCC 1) 1
           (ConstMoney 450)
           10 100
           (When (OrObs (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 0)
                                       (OrObs (PersonChoseThis (IdentChoice 2) 2 0)
                                              (PersonChoseThis (IdentChoice 3) 3 0)))
                               (AndObs (PersonChoseThis (IdentChoice 2) 2 0)
                                       (PersonChoseThis (IdentChoice 3) 3 0)))
                        (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                       (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                              (PersonChoseThis (IdentChoice 3) 3 1)))
                               (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                       (PersonChoseThis (IdentChoice 3) 3 1))))
                 90
                 (Choice (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                        (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                               (PersonChoseThis (IdentChoice 3) 3 1)))
                                (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                        (PersonChoseThis (IdentChoice 3) 3 1)))
                         (Pay (IdentPay 1) 1 2
                              (AvailableMoney (IdentCC 1))
                              100
                              (RedeemCC (IdentCC 1) Null))
                         (RedeemCC (IdentCC 1) Null))
                 (RedeemCC (IdentCC 1) Null))
           Null
```

> __Exercises__
>  
> What other abbreviations could you add to the contract at the top of the page? 
>
> Can you spot any _functions_ that you could define to make the contract shorter, or more modular?


This example has shown how embedding in Haskell gives us a more expressive language, simply by reusing some of the basic features of Haskell, namely definitions of constants and functions. In the next tutorial you will learn about how to exercise Marlowe contracts in ghci.

Notes
- These contracts are contained in the modules [`Escrow.hs`](https://github.com/input-output-hk/marlowe/blob/v1.3/src/Escrow.hs) and [`EscrowV2.hs`](https://github.com/input-output-hk/marlowe/blob/v1.3/src/EscrowV2.hs) in v1.3 of Marlowe. 



### [Prev](./marlowe-semantics.md) [Up](./README.md) [Next](./using-marlowe.md)