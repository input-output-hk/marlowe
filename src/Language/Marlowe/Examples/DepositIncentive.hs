{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.DepositIncentive where

import Language.Marlowe

payAll :: AccountId -> Payee -> Contract -> Contract
payAll acId payee cont =
  Pay acId payee (AvailableMoney acId) cont

contract :: Contract
contract =
  When [ Case (Deposit incentiveAcc incentiviser (incentiveAmt))
              (When [ Case (Deposit depositAcc depositer (depositAmt))
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

depositAcc, incentiveAcc :: AccountId
depositAcc = AccountId 1 depositer
incentiveAcc = AccountId 1 incentiviser

depositer, incentiviser :: Party
depositer = "depositer"
incentiviser = "incentiviser"

