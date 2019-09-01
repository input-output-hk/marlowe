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
  aliceClaims
    when
      carolAgrees
        Refund "alice"       

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

aliceClaims    = Choice (ChoiceId "agree" "alice") [Interval 0 0]
bobClaims      = Choice (ChoiceId "agree" "bob")   [Interval 0 0]
carolAgrees    = Choice (ChoiceId "agree" "carol") [Interval 0 0]
carolDisagrees = Choice (ChoiceId "agree" "carol") [Interval 1 1]


-- Value under escrow
price :: Value
price = Constant 450
