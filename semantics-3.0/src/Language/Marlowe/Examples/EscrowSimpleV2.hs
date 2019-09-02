{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.EscrowSimpleV2 where

import           Language.Marlowe

{- What does the vanilla contract look like?
   Using layout for scoping here

Paraphrase: 
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol can also decide after one of Alice or Bob has acted.             


-}


contract :: Contract
contract = When [Case (Deposit "alice" "alice" price) inner]
                10
                Refund

inner :: Contract

inner =
  When [ Case aliceChoice
              (When [ Case bobChoice 
                          (If (aliceChosen `ValueEQ` bobChosen)
                             agreement
                             arbitrate) ]     
                    60
                    arbitrate),
        Case bobChoice
              (When [ Case aliceChoice 
                          (If (aliceChosen `ValueEQ` bobChosen)
                              agreement
                              arbitrate) ]
                    60
                    arbitrate)
        ]
        40
        Refund

carolCases :: [Case]

carolCases = 
  [ Case carolRefund Refund,
    Case carolPay (Pay "alice" (Party "bob") price Refund)
  ]
              
-- The contract to follow when Alice and Bob have made the same choice.                       
         
agreement :: Contract  

agreement = 
  If 
    (aliceChosen `ValueEQ` (Constant 0))
    (Pay "alice" (Party "bob") price Refund)
    Refund
     
-- The contract to follow when Alice and Bob disagree, or if 
-- Carol wants to intervene after a single choice from Alice or Bob.

arbitrate :: Contract

arbitrate =
  When  carolCases
        100
        Refund

-- Names for choices

pay,refund :: [Bound]

pay    = [Interval 0 0]
refund = [Interval 1 1]
both   = [Interval 0 1]

-- helper function to build Actions

choice :: Party -> [Bound] -> Action

choice party bounds =
  Choice (ChoiceId "choose" party) bounds


-- Name choices according to person making choice and choice made

alicePay, aliceRefund, bobPay, bobRefund, carolPay, carolRefund :: Action

alicePay    = choice "alice" pay
aliceRefund = choice "alice" refund
aliceChoice = choice "alice" both

bobPay    = choice "bob" pay
bobRefund = choice "bob" refund
bobChoice = choice "bob" both

carolPay    = choice "carol" pay
carolRefund = choice "carol" refund
carolChoice = choice "carol" both

-- the values chosen

aliceChosen, bobChosen :: Value

aliceChosen = ChoiceValue (ChoiceId "choice" "alice") defValue
bobChosen   = ChoiceValue (ChoiceId "choice" "bob") defValue

defValue = Constant 42

-- Value under escrow
price :: Value
price = Constant 450
