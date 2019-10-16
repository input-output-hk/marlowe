{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.Rent where

import Language.Marlowe

utility :: Contract
utility = mkDeposit $ payMonth 1 $ payMonth 2 $ payMonth 3 $ Close

tenant, landlord :: Party
tenant = "tenant"
landlord = "landlord"

depositAcc :: AccountId
depositAcc = AccountId 1 tenant

monthlyAcc :: AccountId
monthlyAcc = AccountId 2 tenant

depositAmt, monthlyFee :: Integer
depositAmt = 200
monthlyFee = 120

depositTimeout, daysInAMonth :: Timeout
depositTimeout = 10
daysInAMonth = 30

mkDeposit c = When [Case (Deposit depositAcc tenant (Constant depositAmt))
                         c]
                   depositTimeout
                   Close

payMonth m c = When [Case (Deposit monthlyAcc tenant (Constant monthlyFee))
                          (payAll monthlyAcc (Party landlord) c)]
                    (depositTimeout + m * daysInAMonth)
                    (payAll depositAcc (Party landlord) Close)

-- Pay all money into an account to a payee
payAll :: AccountId -> Payee -> Contract -> Contract
payAll acId payee cont = Pay acId payee (AvailableMoney acId) cont

