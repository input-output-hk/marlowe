module ExpRent where

import Marlowe

expanded =
  When [
    Case (Deposit (AccountId 1 1) 1 (Constant 200))
      (When [
         Case (Deposit (AccountId 2 1) 1 (Constant 120))
           (Pay (AccountId 2 1) (Party 2) (AvailableMoney (AccountId 2 1))
              (When [
                 Case (Deposit (AccountId 2 1) 1 (Constant 120))
                   (Pay (AccountId 2 1) (Party 2) (AvailableMoney (AccountId 2 1))
                      (When [
                         Case (Deposit (AccountId 2 1) 1 (Constant 120))
                           (Pay (AccountId 2 1) (Party 2) (AvailableMoney (AccountId 2 1))
                              Refund)]
                         100
                         (Pay (AccountId 1 1) (Party 2) (AvailableMoney (AccountId 1 1))
                           Refund)))]
                 70
                 (Pay (AccountId 1 1) (Party 2) (AvailableMoney (AccountId 1 1))
                    Refund)))]
         40
         (Pay (AccountId 1 1) (Party 2) (AvailableMoney (AccountId 1 1))
            Refund))]
    10
    Refund


