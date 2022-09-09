{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import qualified Data.Maybe                    as Maybe
import           Control.Monad.State
import           Test.Tasty
import           Test.Tasty.QuickCheck
import           Test.Tasty.HUnit
import           Debug.Trace
import Data.Time

import           Language.Marlowe
import           Language.Marlowe.Examples.ZCBG2

main :: IO ()
main = do
    print $ contractLifespanUpperBound $
        zeroCouponBondGuaranteed ada "investor" "issuer" "guarantor" 1000 200 (POSIXTime 10) (POSIXTime 20)

zeroCouponBond :: Contract i Token
zeroCouponBond = When [ Case
        (Deposit "investor" "investor" ada (Constant 850))
        (Pay "investor" (Party "issuer") ada (Constant 850)
            (When
                [ Case (Deposit "investor" "issuer" ada (Constant 1000))
                        (Pay "investor" (Party "investor") ada (Constant 1000) Close)
                ]
                (POSIXTime 1579305589)
                Close
            )
        )
    ]
    (POSIXTime 1563407989)
    Close

couponBondGuaranteed :: Contract i Token
couponBondGuaranteed = When [Case (Deposit "investor" "guarantor" ada (Constant 1030))
    (When [Case (Deposit "investor" "investor" ada (Constant 1000))
        (Pay "investor" (Party "issuer") ada (Constant 1000)
            (When [Case (Deposit "investor" "issuer" ada (Constant 10))
                (Pay "investor" (Party "investor") ada (Constant 10)
                (Pay "investor" (Party "guarantor") ada (Constant 10)
                    (When [Case (Deposit "investor" "issuer" ada (Constant 10))
                        (Pay "investor" (Party "investor") ada (Constant 10)
                        (Pay "investor" (Party "guarantor") ada (Constant 10)
                            (When [Case (Deposit "investor" "issuer" ada (Constant 1010))
                                (Pay "investor" (Party "investor") ada (Constant 1010)
                                (Pay "investor" (Party "guarantor") ada (Constant 1010) Close))]
                            (POSIXTime 1571788789) Close)))]
                    (POSIXTime 1569196789) Close)))]
            (POSIXTime 1566518389) Close))]
    (POSIXTime 1563839989) Close)]
    (POSIXTime 1563839989) Close


couponBondGuaranteedWithAccounts :: Contract i Token
couponBondGuaranteedWithAccounts =
    -- guarantor deposits a whole payoff amount including interest payments
    When [Case (Deposit "party2" "guarantor" ada (Constant 1030))
        -- then it's same as for simple coupon bond
        (When [Case (Deposit "party1" "party1" ada (Constant 1000))
            (Pay "party1" (Party "party2") ada (Constant 1000)
                (When [Case (Deposit "party1" "party2" ada (Constant 10))
                    (Pay "party1" (Party "party1") ada (Constant 10)
                        (When [Case (Deposit "party1" "party2" ada (Constant 10))
                            (Pay "party1" (Party "party1") ada (Constant 10)
                                (When [Case (Deposit "party1" "party2" ada (Constant 1010))
                                    (Pay "party1" (Party "party1") ada (Constant 1010) Close)]
                                (POSIXTime 1571788789)
                                -- if the issues fails to return notional
                                -- guarantor pays from his account and refunds
                                (Pay "party2" (Party "party1") ada (Constant 1010) Close))
                            )]
                        (POSIXTime 1569196789)
                        -- guarantor pays from his account and refunds
                        (Pay "party2" (Party "party1") ada (Constant 1020) Close)))]
                (POSIXTime 1566518389)
                -- guarantor pays from his account and refunds
                (Pay "party2" (Party "party1") ada (Constant 1030) Close)))]
        -- if partees do not proceed guarantor automatically gets his money back
        (POSIXTime 1563839989) Close)]
    (POSIXTime 1563839989) Close


couponBondGuaranteedWithoutAccounts :: Contract i Token
couponBondGuaranteedWithoutAccounts =
    -- guarantor deposits a whole payoff amount including interest payments
    When [Case (Deposit "party1" "guarantor" ada (Constant 1030))
            -- investor deposits 1000 Ada
        (When [Case (Deposit "party1" "party1" ada (Constant 1000))
            (Pay "party1" (Party "party2") ada (Constant 1000)
                (When [Case (Deposit "party1" "party2" ada (Constant 10))
                    (Pay "party1" (Party "party1") ada (Constant 10)
                        (When [Case (Deposit "party1" "party2" ada (Constant 10))
                            (Pay "party1" (Party "party1") ada (Constant 10)
                                (When [Case (Deposit "party1" "party2" ada (Constant 1010))
                                    (Pay "party1" (Party "party1") ada (Constant 1010) Close)]
                                (POSIXTime 1571788789)
                                (Pay "party1" (Party "party1") ada (Constant 1010)
                                -- with single account we have to
                                -- manually redistibute money to guarantor
                                (Pay "party1" (Party "guarantor") ada (Constant 20) Close))))]
                        (POSIXTime 1569196789)
                        (Pay "party1" (Party "party1") ada (Constant 1020)
                        -- in all the cases
                        (Pay "party1" (Party "guarantor") ada (Constant 10) Close))))]
                (POSIXTime 1566518389)
                -- here as well
                (Pay "party1" (Party "party1") ada (Constant 1030) Close)))]
        (POSIXTime 1563839989)
        -- and thes are only 3 payments
        (Pay "party1" (Party "guarantor") ada (Constant 1030) Close))]
    (POSIXTime 1563839989) Close


{- Simply swap two payments between parties -}
swapExample :: Contract i Token
swapExample =
    When [ Case (Deposit acc1 "party1" ada (Constant 500))
            -- when 1st party committed, wait for 2nd
            (When [ Case (Deposit acc2 "party2" ada (Constant 300))
                (Pay acc1 (Party "party2") ada (Constant 500)
                (Pay acc2 (Party "party1") ada (Constant 300) Close))
                ] date1
            -- if a party dosn't commit, simply Close to the owner
            Close)
          , Case (Deposit acc2 "party2" ada (Constant 300))
            -- if 2nd party committed first wait for 1st
            (When [ Case (Deposit acc1 "party1" ada (Constant 500))
                -- we can just pay a diff between account and refund
                (Pay acc1 (Account acc2) ada (Constant 200) Close)
            ] date1
            -- if a party dosn't commit, simply Close to the owner
            Close)
        ] (date1 - gracePeriod) Close
  where
    gracePeriod = POSIXTime 3*60*24 -- 24 hours
    date1 = POSIXTime 1563839989
    acc1 = "party1"
    acc2 = "party2"

{- Simply swap two payments between parties using single account, fully fungible -}
swapSingleAccount :: Contract i Token
swapSingleAccount =
    When [ Case (Deposit acc1 "party1" ada (Constant 500))
            (When [ Case (Deposit acc1 "party2" ada (Constant 300))
                (Pay acc1 (Party "party2") ada (Constant 500)
                (Pay acc1 (Party "party1") ada (Constant 300) Close))
                ] (POSIXTime date1)
            -- refund to the 1st party
            (Pay acc1 (Party "party1") ada (Constant 500) Close))
         , Case (Deposit acc1 "party2" ada (Constant 300))
            (When [ Case (Deposit acc1 "party1" ada (Constant 500))
                (Pay acc1 (Party "party2") ada (Constant 500)
                (Pay acc1 (Party "party1") ada (Constant 300) Close))
            ] (POSIXTime date1)
            -- refund to the 2nd party
            (Pay acc1 (Party "party2") ada (Constant 300) Close))
        ] (POSIXTime (date1 - gracePeriod)) Close
  where
    gracePeriod = 3*60*24 -- 24 hours
    date1 = 1563839989
    acc1 = "party1"
    acc2 = "party2"

{- Swap two payments between parties, all payments are guaranteed by a 3rd party -}
swapGuaranteedExample :: Contract i Token
swapGuaranteedExample =
    When [ Case (Deposit acc3 "guarantor" ada (Constant 800))
        (When [
            Case (Deposit acc1 "party1" ada (Constant 500))
                (When [ Case (Deposit acc2 "party2" ada (Constant 300))
                    (Pay acc1 (Party "party2") ada (Constant 500)
                    (Pay acc2 (Party "party1") ada (Constant 300) Close))
                    ] date1
                    -- just transfer from guarantor account to party1 and refund to owner
                    (Pay acc3 (Account acc1) ada (Constant 300) Close))
            , Case (Deposit acc2 "party2" ada (Constant 300))
                (When [ Case (Deposit acc2 "party2" ada (Constant 500))
                    (Pay acc1 (Party "party2") ada (Constant 500)
                    (Pay acc2 (Party "party1") ada (Constant 300) Close))
                    ] date1
                    -- just transfer from guarantor account to party1 and refund to owner
                    (Pay acc3 (Account acc2) ada (Constant 500) Close))
            ] (date1 - gracePeriod)
            -- automatically refund to guarantor if parties don't proceed
            Close)
        ] (date1 - 2 * gracePeriod) Close
  where
    gracePeriod = POSIXTime 3*60*24 -- 24 hours
    date1 = POSIXTime 1563839989
    acc1 = "party1"
    acc2 = "party2"
    acc3 = "guarantor"

{-  Swap two payments between parties using single account.
    All payments are guaranteed by a 3rd party.
-}
swapSingleAccountGuaranteedExample :: Contract i Token
swapSingleAccountGuaranteedExample =
    When [ Case (Deposit acc1 "guarantor" ada (Constant 800))
        (When [
            Case (Deposit acc1 "party1" ada (Constant 500))
                (When [ Case (Deposit acc1 "party2" ada (Constant 300))
                    (Pay acc1 (Party "party2") ada (Constant 500)
                    (Pay acc1 (Party "party1") ada (Constant 300)
                    (Pay acc1 (Party "guarantor") ada (Constant 800) Close)))
                    ] date1
                    -- with single account all payments must be duplicated
                    (Pay acc1 (Party "party2") ada (Constant 500)
                    (Pay acc1 (Party "party1") ada (Constant 300)
                    (Pay acc1 (Party "guarantor") ada (Constant 500) Close)))
                )
            , Case (Deposit acc2 "party2" ada (Constant 300))
                (When [ Case (Deposit acc2 "party2" ada (Constant 500))
                    (Pay acc1 (Party "party2") ada (Constant 500)
                    (Pay acc1 (Party "party1") ada (Constant 300)
                    (Pay acc1 (Party "guarantor") ada (Constant 800) Close)))
                    ] date1
                    -- with single account all payments must be duplicated
                    (Pay acc1 (Party "party2") ada (Constant 500)
                    (Pay acc1 (Party "party1") ada (Constant 300)
                    (Pay acc1 (Party "guarantor") ada (Constant 00) Close)))
                )
            ] (date1 - gracePeriod)
            -- manually refund to guarantor if parties don't proceed
            (Pay acc1 (Party "guarantor") ada (Constant 800) Close))
        ] (date1 - 2 * gracePeriod) Close
    where
    gracePeriod = POSIXTime 3*60*24 -- 24 hours
    date1 = POSIXTime 1563839989
    acc1 = "party1"
    acc2 = "party2"
    acc3 = "guarantor"

choiceIdExample :: ChoiceId i
choiceIdExample = ChoiceId "RockPaperScissors" "Alice"
