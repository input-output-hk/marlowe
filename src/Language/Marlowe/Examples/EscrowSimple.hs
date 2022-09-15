{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.EscrowSimple where

import           Language.Marlowe

{- What does the vanilla contract look like?
   Using layout for scoping here

When
  bobClaims
    when
      carolAgrees
        Pay "alice" "bob" tok price
      carolDisagrees
        Close "alice"
  aliceClaims
    when
      carolAgrees
        Close "alice"
      carolDisagrees
        Pay "alice" "bob" tok price

-}

contract :: t -> Contract i t
contract tok = When [Case (Deposit "alice" "alice" tok price)
                          (When [ processBobClaim tok
                                , processAliceClaim tok
                                ]
                                90
                                Close)
                    ]
                    10
                    Close

processBobClaim, processAliceClaim :: t -> Case i t

processBobClaim tok =
  Case bobClaims
    (When [ Case carolAgrees (Pay "alice" (Party "bob") tok price Close)
          , Case carolDisagrees Close
          ]
         100
         Close)

processAliceClaim tok =
  Case aliceClaims
    (When [ Case carolAgrees Close,
            Case carolDisagrees (Pay "alice" (Party "bob") tok price Close)
          ]
       100
       Close)

aliceClaims, bobClaims, carolAgrees, carolDisagrees :: Action i t

aliceClaims    = Choice (ChoiceId "claim" "alice") [Bound 0 0]
bobClaims      = Choice (ChoiceId "claim" "bob")   [Bound 0 0]
carolAgrees    = Choice (ChoiceId "agree" "carol") [Bound 0 0]
carolDisagrees = Choice (ChoiceId "agree" "carol") [Bound 1 1]


-- Value under escrow
price :: Value i t
price = Constant 450
