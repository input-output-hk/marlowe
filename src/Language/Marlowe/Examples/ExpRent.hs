{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.ExpRent where

import Language.Marlowe

expanded =
  When [
    Case (Deposit (AccountId 1 "party1") "party1" (Constant 200))
      (When [
         Case (Deposit (AccountId 2 "party1") "party1" (Constant 120))
           (Pay (AccountId 2 "party1") (Party "party2") (AvailableMoney (AccountId 2 "party1"))
              (When [
                 Case (Deposit (AccountId 2 "party1") "party1" (Constant 120))
                   (Pay (AccountId 2 "party1") (Party "party2") (AvailableMoney (AccountId 2 "party1"))
                      (When [
                         Case (Deposit (AccountId 2 "party1") "party1" (Constant 120))
                           (Pay (AccountId 2 "party1") (Party "party2") (AvailableMoney (AccountId 2 "party1"))
                              Close)]
                         100
                         (Pay (AccountId 1 "party1") (Party "party2") (AvailableMoney (AccountId 1 "party1"))
                           Close)))]
                 70
                 (Pay (AccountId 1 "party1") (Party "party2") (AvailableMoney (AccountId 1 "party1"))
                    Close)))]
         40
         (Pay (AccountId 1 "party1") (Party "party2") (AvailableMoney (AccountId 1 "party1"))
            Close))]
    10
    Close


