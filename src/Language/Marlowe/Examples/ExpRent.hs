{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.ExpRent where

import Language.Marlowe

expanded =
  When [Case (Deposit "tenantDeposit" "tenant" (Constant 200))
    (When [Case (Deposit "tenant" "tenant" (Constant 120))
      (Pay "tenant" (Party "landlord") (AvailableMoney "tenant")
        (When [Case (Deposit "tenant" "tenant" (Constant 120))
          (Pay "tenant" (Party "landlord") (AvailableMoney "tenant")
            (When [Case (Deposit "tenant" "tenant" (Constant 120))
              (Pay "tenant" (Party "landlord") (AvailableMoney "tenant") Close)]
            100 (Pay "tenantDeposit" (Party "landlord") (AvailableMoney "tenantDeposit") Close)))]
        70 (Pay "tenantDeposit" (Party "landlord") (AvailableMoney "tenantDeposit") Close)))]
    40 (Pay "tenantDeposit" (Party "landlord") (AvailableMoney "tenantDeposit") Close))]
  10 Close


