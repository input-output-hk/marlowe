{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.Rent where

import Language.Marlowe

utilityMonths :: t -> Integer -> Contract i t
utilityMonths tok n = foldl (.) (mkDeposit tok) [payMonth tok (POSIXTime x) | x <- [1..n]] Close

utility :: t -> Contract i t
utility tok = mkDeposit tok $ payMonth tok 1 $ payMonth tok 2 $ payMonth tok 3 $ Close

tenant, landlord, tenantDeposit :: Party i
tenant = Role "tenant"
tenantDeposit = Role  "tenantDeposit"
landlord = Role "landlord"

depositAcc :: Party i
depositAcc = tenantDeposit

monthlyAcc :: Party i
monthlyAcc = tenant

depositAmt, monthlyFee :: Integer
depositAmt = 200
monthlyFee = 120

depositTimeout, daysInAMonth :: Timeout
depositTimeout = 10
daysInAMonth = 30

mkDeposit :: t -> Contract i t -> Contract i t
mkDeposit tok c = When [Case (Deposit tenantDeposit tenant tok (Constant depositAmt))
                             c]
                       depositTimeout
                       Close

payMonth :: t -> Timeout -> Contract i t -> Contract i t
payMonth tok m c = When [Case (Deposit monthlyAcc tenant tok (Constant monthlyFee))
                              (payAll tok monthlyAcc (Party landlord) c)]
                        (depositTimeout + m * daysInAMonth)
                        (payAll tok depositAcc (Party landlord) Close)

-- Pay all money into an account to a payee
payAll :: t -> Party i -> Payee i -> Contract i t -> Contract i t
payAll tok acId payee = Pay acId payee tok (AvailableMoney acId tok)

