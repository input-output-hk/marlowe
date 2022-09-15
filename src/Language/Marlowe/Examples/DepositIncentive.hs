{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.DepositIncentive where

import Language.Marlowe

payAll :: t -> Party i -> Payee i -> Contract i t -> Contract i t
payAll tok acId payee = Pay acId payee tok (AvailableMoney acId tok)

contract :: t -> Contract i t
contract tok =
  When [ Case (Deposit incentiveAcc incentiviser tok incentiveAmt)
              (When [ Case (Deposit depositAcc depositer tok depositAmt)
                           (When [ Case (Choice (ChoiceId "refund" depositer) [Bound 1 1])
                                        Close
                                 ]
                                 200
                                 (payAll tok
                                         incentiveAcc (Account depositAcc)
                                         Close))
                    ]
                    20
                    Close)
       ]
       10
       Close

depositAmt, incentiveAmt :: Value i t
depositAmt = Constant 100
incentiveAmt = Constant 20

depositAcc, incentiveAcc :: Party i
depositAcc = depositer
incentiveAcc = incentiviser

depositer, incentiviser :: Party i
depositer = "depositer"
incentiviser = "incentiviser"

