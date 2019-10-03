{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.EscrowSimple where

import           Language.Marlowe

{- What does the vanilla contract look like?
   Using layout for scoping here

When
  bobClaims
    when
      carolAgrees
        Pay "alice" "bob" price
      carolDisagrees
        Refund "alice"       
  aliceClaims
    when
      carolAgrees
        Refund "alice"       
      carolDisagrees
        Pay "alice" "bob" price

-}

contract :: Contract
contract = When [Case (Deposit "alice" "alice" price)
                      (When [ processBobClaim
                            , processAliceClaim 
                            ]
                            90
                            Refund)
                ]
                10
                Refund

processBobClaim, processAliceClaim :: Case

processBobClaim =
  Case bobClaims 
    (When [ Case carolAgrees (Pay "alice" (Party "bob") price Refund)
          , Case carolDisagrees Refund
          ]
         100
         Refund)

processAliceClaim = 
  Case aliceClaims 
    (When [ Case carolAgrees Refund,
            Case carolDisagrees (Pay "alice" (Party "bob") price Refund) 
          ]
       100
       Refund)

aliceClaims, bobClaims, carolAgrees, carolDisagrees :: Action

aliceClaims    = Choice (ChoiceId "claim" "alice") [Bound 0 0]
bobClaims      = Choice (ChoiceId "claim" "bob")   [Bound 0 0]
carolAgrees    = Choice (ChoiceId "agree" "carol") [Bound 0 0]
carolDisagrees = Choice (ChoiceId "agree" "carol") [Bound 1 1]


-- Value under escrow
price :: Value
price = Constant 450
