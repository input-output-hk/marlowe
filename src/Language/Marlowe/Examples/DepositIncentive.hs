{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.DepositIncentive where

import Language.Marlowe

payAll :: Party -> Payee -> Contract -> Contract
payAll acId payee = Pay acId payee ada (AvailableMoney acId ada)

contract :: Contract
contract =
  When [ Case (Deposit incentiveAcc incentiviser ada incentiveAmt)
              (When [ Case (Deposit depositAcc depositer ada depositAmt)
                           (When [ Case (Choice (ChoiceId "refund" depositer) [Bound 1 1])
                                        Close
                                 ]
                                 200
                                 (payAll incentiveAcc (Account depositAcc)
                                         Close))
                    ]
                    20
                    Close)
       ]
       10
       Close

depositAmt, incentiveAmt :: Value
depositAmt = Constant 100
incentiveAmt = Constant 20

depositAcc, incentiveAcc :: Party
depositAcc = depositer
incentiveAcc = incentiviser

depositer, incentiviser :: Party
depositer = "depositer"
incentiviser = "incentiviser"

