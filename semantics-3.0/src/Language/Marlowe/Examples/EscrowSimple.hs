{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.EscrowSimple where

import           Language.Marlowe

{- What does the vanilla contract look like?
   Using layout for scoping here

When
  bobAgrees
    when
      carolAgrees
        Pay "alice" "bob" price
  aliceAgrees
    when
      carolAgrees
        Refund "alice"       

-}

contract :: Contract
contract = When [Case (Deposit "alice" "alice" price)
                      (When [ makePaymentToBob
                            , refundToAlice 
                            ]
                            50
                            Refund)
                ]
                10
                Refund

makePaymentToBob, refundToAlice :: Case

makePaymentToBob =
  Case bobAgrees 
    (When [Case carolAgrees (Pay "alice" (Party "bob") price Refund)]
         90
         Refund)

refundToAlice = 
  Case aliceAgrees 
    (When [Case carolAgrees Refund]
       90
       Refund)

aliceAgrees, bobAgrees, carolAgrees :: Action

aliceAgrees = Choice (ChoiceId "agree" "alice") [Interval 0 0]
bobAgrees   = Choice (ChoiceId "agree" "bob")   [Interval 0 0]
carolAgrees = Choice (ChoiceId "agree" "carol") [Interval 0 0]


-- Value under escrow
price :: Value
price = Constant 450
