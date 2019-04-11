# Embedded Marlowe

In this tutorial we go back to the escrow example, and show how we can use the _embedding_ of Marlowe in Haskell to make more readable, modular and reusable descriptions of Marlowe contracts.

## A simple escrow contract, revisited.

![Escrow](./pix/escrow.png)

Recall that we developed this Marlowe contract in our [earlier tutorial](./escrow-ex.md).

```haskell
Commit 1 iCC1 alice (Constant 450) 10 100
                  (When (OrObs (two_chose alice bob carol refund)
                               (two_chose alice bob carol pay))
                        90
                        (Choice (two_chose alice bob carol pay)
                                (Pay 2 iCC1 bob (Committed iCC1) 100 Null Null)
                                redeem_original 3)
                        redeem_original 4)
        Null
```

This contract makes use of the fact that Haskell allows definitions of simple abbreviations, such as

```haskell
-- Participants

alice, bob, carol :: Person

alice = 1
bob   = 2
carol = 3

-- Possible votes

refund, pay :: Choice

refund = 0
pay    = 1

```

which make our contracts more readable. Indeed Marlowe could be extended to include more meaningful ‘atomic’ data, but in our design we chose to keep such constructs to a minimum. We can also give more meaningful abbreviations for contracts and identifiers:

```haskell
-- Redeem original with action id 3.

redeem_original_3 :: Contract

redeem_original_3 = Pay 3 iCC1 alice (Committed iCC1) 100 Null Null

-- Commit identifier

iCC1 :: IdCommit

iCC1 = 1
```

As well as defining constants, it is possible to define simple functions too, including 

```haskell
-- Majority choice

majority_chose :: Choice -> Contract

majority_chose x = two_chose alice bob carol x
```

giving the simpler contract:

```haskell
Commit 1 iCC1 alice (Constant 450) 10 100
                  (When (OrObs (majority_chose refund)
                               (majority_chose pay))
                        90
                        (Choice (majority_chose pay)
                                (Pay 2 iCC1 bob (Committed iCC1) 100 Null Null)
                                redeem_original 3)
                        redeem_original 4)
        Null
```

Looking now in more detail at the other definitions used in the contract, we first define

```haskell
chose :: Integer -> Choice -> Observation

chose per c = ChoseThis (1, per) c
```

```haskell
chose :: Int -> ConcreteChoice -> Observation

chose per c = 
        PersonChoseThis (IdentChoice per) per c
```

**WHAT IS THE ROLE OF `1` HERE??** which encapsulates the choice of `c` by person `per`, identifying it with identifier `1`.  (Of course, in other situations we will need to be more careful about how we use identifiers).

Given this definition we can give a description of the observation of one person (at least) choosing a particular option

```haskell
one_chose :: Person -> Person -> Choice -> Observation

one_chose per per' val = (OrObs (chose per val) (chose per' val))
 ```

 and using that describe the choice being made by two out of three:

 ```haskell
two_chose :: Person -> Person -> Person -> Choice -> Observation

two_chose p1 p2 p3 c = OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))
                              (AndObs (chose p2 c) (chose p3 c))
```

Given all these definitions, we are able to write the contract at the start of this section in a way that makes its intention clear. Writing in “pure” Marlowe, or by expanding out these definitions, we would have this contract instead:

```haskell
Commit 1 1 1
  (Constant 450) 10 100
  (When
     (OrObs
        (OrObs
           (AndObs
              (ChoseThis (1, 1) 0)
              (OrObs
                 (ChoseThis (1, 2) 0)
                 (ChoseThis (1, 3) 0)))
           (AndObs
              (ChoseThis (1, 2) 0)
              (ChoseThis (1, 3) 0)))
        (OrObs
           (AndObs
              (ChoseThis (1, 1) 1)
              (OrObs
                 (ChoseThis (1, 2) 1)
                 (ChoseThis (1, 3) 1)))
           (AndObs
              (ChoseThis (1, 2) 1)
              (ChoseThis (1, 3) 1)))) 90
     (Choice
        (OrObs
           (AndObs
              (ChoseThis (1, 1) 1)
              (OrObs
                 (ChoseThis (1, 2) 1)
                 (ChoseThis (1, 3) 1)))
           (AndObs
              (ChoseThis (1, 2) 1)
              (ChoseThis (1, 3) 1)))
        (Pay 2 1 2
           (Committed 1) 100 Null Null)
        (Pay 3 1 1
           (Committed 1) 100 Null Null))
     (Pay 4 1 1
        (Committed 1) 100 Null Null)) Null
```

> __Exercises__
>  
> What other abbreviations could you add to the contract at the top of the page? 
>
> Can you spot any _functions_ that you could define to make the contract shorter, or more modular?


This example has shown how embedding in Haskell gives us a more expressive language, simply by reusing some of the basic features of Haskell, namely definitions of constants and functions. In the next tutorial you will learn about how to exercise Marlowe contracts in ghci.

### Note

- **TO UPDATE: LINKS BELOW**
- These contracts are contained in the modules [`Escrow.hs`](https://github.com/input-output-hk/marlowe/blob/v1.3/src/Escrow.hs) and [`EscrowV2.hs`](https://github.com/input-output-hk/marlowe/blob/v1.3/src/EscrowV2.hs) in v2.0 of Marlowe. 



### [Prev](./marlowe-semantics.md) [Up](./README.md) [Next](./using-marlowe.md)