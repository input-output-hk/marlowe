module DepositIncentive where

import Marlowe

payAll :: AccountId -> Payee -> Contract -> Contract
payAll acId payee cont =
  Pay acId payee (AvailableMoney acId) cont

contract :: Contract
contract =
  When [ Case (Deposit incentiveAcc incentiviser (incentiveAmt))
              (When [ Case (Deposit depositAcc depositer (depositAmt))
                           (When [ Case (Choice (ChoiceId 1 depositer) [(1,1)])
                                        Refund
                                 ]
                                 200
                                 (payAll incentiveAcc (Account depositAcc)
                                         Refund))
                    ]
                    20
                    Refund)
       ]
       10
       Refund

depositAmt, incentiveAmt :: Value
depositAmt = Constant 100
incentiveAmt = Constant 20

depositAcc, incentiveAcc :: AccountId
depositAcc = AccountId 1 depositer
incentiveAcc = AccountId 1 incentiviser

depositer, incentiviser :: Party
depositer = 1
incentiviser = 2

