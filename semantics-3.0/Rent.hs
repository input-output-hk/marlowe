module Rent where

import Semantics4

utility :: Contract
utility = mkDeposit $ payMonth 1 $ payMonth 2 $ payMonth 3 $ Refund

tenant, landlord :: Party
tenant = 1
landlord = 2

depositAcc :: AccountId
depositAcc = AccountId 1 tenant

monthlyAcc :: AccountId
monthlyAcc = AccountId 2 tenant

depositAmt, monthlyFee :: Money
depositAmt = 200
monthlyFee = 120

mkDeposit c = When [Case (Deposit depositAcc tenant (Constant depositAmt))
                         c]
                   10
                   Refund

payMonth m c = When [Case (Deposit monthlyAcc tenant (Constant monthlyFee))
                          (payAll monthlyAcc (Party landlord) c)]
                    (10 + m * 30)
                    (payAll depositAcc (Party landlord) Refund)

-- Pay all money into an account to a payee
payAll :: AccountId -> Payee -> Contract -> Contract
payAll acId payee cont = Pay acId payee (AvailableMoney acId) cont

