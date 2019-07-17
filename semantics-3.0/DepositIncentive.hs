module DepositIncentive where

import Semantics4

payAll :: AccountId -> Payee -> Contract -> Contract
payAll acId payee cont =
  Pay acId payee (AvailableMoney acId) cont

contract :: Contract
contract =
  When [ Case (Deposit incentiveAcc incentiviser (incentiveAmt))
              (When [ Case (Deposit depositAcc depositer (depositAmt))
                           (When [ Case (Choice (ChoiceId 1 depositer) [(1,1)])
                                        RefundAll
                                 ]
                                 200
                                 (payAll incentiveAcc (Account depositAcc)
                                         RefundAll))
                    ]
                    20
                    RefundAll)
       ]
       10
       RefundAll

depositAmt, incentiveAmt :: Value
depositAmt = Constant 100
incentiveAmt = Constant 20

depositAcc, incentiveAcc :: AccountId 
depositAcc = AccountId 1 depositer
incentiveAcc = AccountId 1 incentiviser

depositer, incentiviser :: Party
depositer = 1
incentiviser = 2

