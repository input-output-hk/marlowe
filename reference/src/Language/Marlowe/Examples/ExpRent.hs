{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.ExpRent where

import Language.Marlowe

expanded =
  When [Case (Deposit "tenantDeposit" "tenant" ada (Constant 200))
    (When [Case (Deposit "tenant" "tenant" ada (Constant 120))
      (Pay "tenant" (Party "landlord") ada (AvailableMoney "tenant" ada)
        (When [Case (Deposit "tenant" "tenant" ada (Constant 120))
          (Pay "tenant" (Party "landlord") ada (AvailableMoney "tenant" ada)
            (When [Case (Deposit "tenant" "tenant" ada (Constant 120))
              (Pay "tenant" (Party "landlord") ada (AvailableMoney "tenant" ada) Close)]
            100 (Pay "tenantDeposit" (Party "landlord") ada (AvailableMoney "tenantDeposit" ada) Close)))]
        70 (Pay "tenantDeposit" (Party "landlord") ada (AvailableMoney "tenantDeposit" ada) Close)))]
    40 (Pay "tenantDeposit" (Party "landlord") ada (AvailableMoney "tenantDeposit" ada) Close))]
  10 Close


