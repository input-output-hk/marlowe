{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.Rent where

import Language.Marlowe

utilityMonths :: Integer -> Contract
utilityMonths n = foldl (.) mkDeposit [payMonth (POSIXTime x) | x <- [1..n]] Close

utility :: Contract
utility = mkDeposit $ payMonth 1 $ payMonth 2 $ payMonth 3 $ Close

tenant, landlord, tenantDeposit :: Party
tenant = "tenant"
tenantDeposit = "tenantDeposit"
landlord = "landlord"

depositAcc :: Party
depositAcc = tenantDeposit

monthlyAcc :: Party
monthlyAcc = tenant

depositAmt, monthlyFee :: Integer
depositAmt = 200
monthlyFee = 120

depositTimeout, daysInAMonth :: Timeout
depositTimeout = 10
daysInAMonth = 30

mkDeposit c = When [Case (Deposit tenantDeposit tenant ada (Constant depositAmt))
                         c]
                   depositTimeout
                   Close

payMonth m c = When [Case (Deposit monthlyAcc tenant ada (Constant monthlyFee))
                          (payAll monthlyAcc (Party landlord) c)]
                    (depositTimeout + m * daysInAMonth)
                    (payAll depositAcc (Party landlord) Close)

-- Pay all money into an account to a payee
payAll :: Party -> Payee -> Contract -> Contract
payAll acId payee = Pay acId payee ada (AvailableMoney acId ada)

