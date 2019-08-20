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

import           Semantics
import           ZCBG2
import           ActusContracts

main :: IO ()
main = do
    print $ contractLifespan $ zeroCouponBondGuaranteed 1 2 3 1000 200 (Slot 10) (Slot 20)
    now <- getCurrentTime
    let td = utctDay now
    let couponBondFor3Month12PercentConfig = cb td (addGregorianMonthsClip 3 td) 1000 0.12
    let zcbConfig = zcb td (addGregorianMonthsClip 6 td) 1000 (-150)
    print $ genPrincialAtMaturnityContract 1 2 couponBondFor3Month12PercentConfig
    print $ genPrincialAtMaturnityGuaranteedContract 1 2 3 couponBondFor3Month12PercentConfig
    print $ genPrincialAtMaturnityContract 1 2 zcbConfig


couponBondFor3Month12Percent =
    -- investor deposits 1000 Ada
    When [ Case (Deposit acc investor (Constant 1000))
        -- and pays it to the issuer
        (Pay acc (Party issuer) (Constant 1000)
            -- after a month expect to receive 10 Ada interest
            (When [ Case (Deposit acc issuer (Constant 10))
                -- and pay it to the investor
                (Pay acc (Party investor) (Constant 10)
                    -- same for 2nd month
                    (When [ Case (Deposit acc issuer (Constant 10))
                        (Pay acc (Party investor) (Constant 10)
                            -- after maturity date investor
                            -- expects to receive notional + interest payment
                            (When [ Case (Deposit acc issuer (Constant 1010))
                                (Pay acc (Party investor) (Constant 1010) Refund)]
                            (Slot 1571788789)
                            Refund))]
                    (Slot 1569196789)
                    Refund))]
            (Slot 1566518389)
            Refund))]
    (Slot 1563839989)
    Refund
  where
    acc = AccountId 1 1
    investor = 1
    issuer = 2


zeroCouponBond = When [ Case
        (Deposit acc 1 (Constant 850))
        (Pay acc (Party 2) (Constant 850)
            (When
                [ Case (Deposit acc 2 (Constant 1000))
                        (Pay acc (Party 1) (Constant 1000) Refund)
                ]
                (Slot 1579305589)
                Refund
            )
        )
    ]
    (Slot 1563407989)
    Refund
  where
    acc = AccountId 1 1
    investor = Party 1
    issuer = Party 2

couponBondGuaranteed = When [Case (Deposit acc 3 (Constant 1030))
    (When [Case (Deposit acc 1 (Constant 1000))
        (Pay acc (Party 2) (Constant 1000)
            (When [Case (Deposit acc 2 (Constant 10))
                (Pay acc (Party 1) (Constant 10)
                (Pay acc (Party 3) (Constant 10)
                    (When [Case (Deposit acc 2 (Constant 10))
                        (Pay acc (Party 1) (Constant 10)
                        (Pay acc (Party 3) (Constant 10)
                            (When [Case (Deposit acc 2 (Constant 1010))
                                (Pay acc (Party 1) (Constant 1010)
                                (Pay acc (Party 3) (Constant 1010) Refund))]
                            (Slot 1571788789) Refund)))]
                    (Slot 1569196789) Refund)))]
            (Slot 1566518389) Refund))]
    (Slot 1563839989) Refund)]
    (Slot 1563839989) Refund
  where
    acc = AccountId 1 1
    investor = Party 1
    issuer = Party 2


couponBondGuaranteedWithAccounts =
    -- guarantor deposits a whole payoff amount including interest payments
    When [Case (Deposit acc2 guarantor (Constant 1030))
        -- then it's same as for simple coupon bond
        (When [Case (Deposit acc1 party1 (Constant 1000))
            (Pay acc1 (Party party2) (Constant 1000)
                (When [Case (Deposit acc1 party2 (Constant 10))
                    (Pay acc1 (Party party1) (Constant 10)
                        (When [Case (Deposit acc1 party2 (Constant 10))
                            (Pay acc1 (Party party1) (Constant 10)
                                (When [Case (Deposit acc1 party2 (Constant 1010))
                                    (Pay acc1 (Party party1) (Constant 1010) Refund)]
                                (Slot 1571788789)
                                -- if the issues fails to return notional
                                -- guarantor pays from his account and refunds
                                (Pay acc2 (Party party1) (Constant 1010) Refund))
                            )]
                        (Slot 1569196789)
                        -- guarantor pays from his account and refunds
                        (Pay acc2 (Party party1) (Constant 1020) Refund)))]
                (Slot 1566518389)
                -- guarantor pays from his account and refunds
                (Pay acc2 (Party party1) (Constant 1030) Refund)))]
        -- if partees do not proceed guarantor automatically gets his money back
        (Slot 1563839989) Refund)]
    (Slot 1563839989) Refund
  where
    party1 = 1
    party2 = 2
    guarantor = 3
    acc1 = AccountId 1 party1
    acc2 = AccountId 2 guarantor


couponBondGuaranteedWithoutAccounts =
    -- guarantor deposits a whole payoff amount including interest payments
    When [Case (Deposit acc guarantor (Constant 1030))
            -- investor deposits 1000 Ada
        (When [Case (Deposit acc party1 (Constant 1000))
            (Pay acc (Party party2) (Constant 1000)
                (When [Case (Deposit acc party2 (Constant 10))
                    (Pay acc (Party party1) (Constant 10)
                        (When [Case (Deposit acc party2 (Constant 10))
                            (Pay acc (Party party1) (Constant 10)
                                (When [Case (Deposit acc party2 (Constant 1010))
                                    (Pay acc (Party party1) (Constant 1010) Refund)]
                                (Slot 1571788789)
                                (Pay acc (Party party1) (Constant 1010)
                                -- with single account we have to
                                -- manually redistibute money to guarantor
                                (Pay acc (Party guarantor) (Constant 20) Refund))))]
                        (Slot 1569196789)
                        (Pay acc (Party party1) (Constant 1020)
                        -- in all the cases
                        (Pay acc (Party guarantor) (Constant 10) Refund))))]
                (Slot 1566518389)
                -- here as well
                (Pay acc (Party party1) (Constant 1030) Refund)))]
        (Slot 1563839989)
        -- and thes are only 3 payments
        (Pay acc (Party guarantor) (Constant 1030) Refund))]
    (Slot 1563839989) Refund
  where
    party1 = 1
    party2 = 2
    guarantor = 3
    acc = AccountId 1 party1

{- Simply swap two payments between parties -}
swapExample =
    When [ Case (Deposit acc1 party1 (Constant 500))
            -- when 1st party committed, wait for 2nd
            (When [ Case (Deposit acc2 party2 (Constant 300))
                (Pay acc1 (Party party2) (Constant 500)
                (Pay acc2 (Party party1) (Constant 300) Refund))
                ] date1
            -- if a party dosn't commit, simply Refund to the owner
            Refund)
          , Case (Deposit acc2 party2 (Constant 300))
            -- if 2nd party committed first wait for 1st
            (When [ Case (Deposit acc1 party1 (Constant 500))
                -- we can just pay a diff between account and refund
                (Pay acc1 (Account acc2) (Constant 200) Refund)
            ] date1
            -- if a party dosn't commit, simply Refund to the owner
            Refund)
        ] (date1 - gracePeriod) Refund
  where
    party1 = 1
    party2 = 2
    gracePeriod = Slot 3*60*24 -- 24 hours
    date1 = Slot 1563839989
    acc1 = AccountId 1 party1
    acc2 = AccountId 2 party2

{- Simply swap two payments between parties using single account, fully fungible -}
swapSingleAccount =
    When [ Case (Deposit acc1 party1 (Constant 500))
            (When [ Case (Deposit acc1 party2 (Constant 300))
                (Pay acc1 (Party party2) (Constant 500)
                (Pay acc1 (Party party1) (Constant 300) Refund))
                ] (Slot date1)
            -- refund to the 1st party
            (Pay acc1 (Party party1) (Constant 500) Refund))
         , Case (Deposit acc1 party2 (Constant 300))
            (When [ Case (Deposit acc1 party1 (Constant 500))
                (Pay acc1 (Party party2) (Constant 500)
                (Pay acc1 (Party party1) (Constant 300) Refund))
            ] (Slot date1)
            -- refund to the 2nd party
            (Pay acc1 (Party party2) (Constant 300) Refund))
        ] (Slot (date1 - gracePeriod)) Refund
  where
    party1 = 1
    party2 = 2
    gracePeriod = 3*60*24 -- 24 hours
    date1 = 1563839989
    acc1 = AccountId 1 party1
    acc2 = AccountId 2 party2

{- Swap two payments between parties, all payments are guaranteed by a 3rd party -}
swapGuaranteedExample =
    When [ Case (Deposit acc3 guarantor (Constant 800))
        (When [
            Case (Deposit acc1 party1 (Constant 500))
                (When [ Case (Deposit acc2 party2 (Constant 300))
                    (Pay acc1 (Party party2) (Constant 500)
                    (Pay acc2 (Party party1) (Constant 300) Refund))
                    ] date1
                    -- just transfer from guarantor account to party1 and refund to owner
                    (Pay acc3 (Account acc1) (Constant 300) Refund))
            , Case (Deposit acc2 party2 (Constant 300))
                (When [ Case (Deposit acc2 party2 (Constant 500))
                    (Pay acc1 (Party party2) (Constant 500)
                    (Pay acc2 (Party party1) (Constant 300) Refund))
                    ] date1
                    -- just transfer from guarantor account to party1 and refund to owner
                    (Pay acc3 (Account acc2) (Constant 500) Refund))
            ] (date1 - gracePeriod)
            -- automatically refund to guarantor if parties don't proceed
            Refund)
        ] (date1 - 2 * gracePeriod) Refund
  where
    party1 = 1
    party2 = 2
    guarantor = 3
    gracePeriod = Slot 3*60*24 -- 24 hours
    date1 = Slot 1563839989
    acc1 = AccountId 1 party1
    acc2 = AccountId 2 party2
    acc3 = AccountId 3 guarantor

{-  Swap two payments between parties using single account.
    All payments are guaranteed by a 3rd party.
-}
swapSingleAccountGuaranteedExample =
    When [ Case (Deposit acc1 guarantor (Constant 800))
        (When [
            Case (Deposit acc1 party1 (Constant 500))
                (When [ Case (Deposit acc1 party2 (Constant 300))
                    (Pay acc1 (Party party2) (Constant 500)
                    (Pay acc1 (Party party1) (Constant 300)
                    (Pay acc1 (Party guarantor) (Constant 800) Refund)))
                    ] date1
                    -- with single account all payments must be duplicated
                    (Pay acc1 (Party party2) (Constant 500)
                    (Pay acc1 (Party party1) (Constant 300)
                    (Pay acc1 (Party guarantor) (Constant 500) Refund)))
                )
            , Case (Deposit acc2 party2 (Constant 300))
                (When [ Case (Deposit acc2 party2 (Constant 500))
                    (Pay acc1 (Party party2) (Constant 500)
                    (Pay acc1 (Party party1) (Constant 300)
                    (Pay acc1 (Party guarantor) (Constant 800) Refund)))
                    ] date1
                    -- with single account all payments must be duplicated
                    (Pay acc1 (Party party2) (Constant 500)
                    (Pay acc1 (Party party1) (Constant 300)
                    (Pay acc1 (Party guarantor) (Constant 00) Refund)))
                )
            ] (date1 - gracePeriod)
            -- manually refund to guarantor if parties don't proceed
            (Pay acc1 (Party guarantor) (Constant 800) Refund))
        ] (date1 - 2 * gracePeriod) Refund
    where
    party1 = 1
    party2 = 2
    guarantor = 3
    gracePeriod = Slot 3*60*24 -- 24 hours
    date1 = Slot 1563839989
    acc1 = AccountId 1 party1
    acc2 = AccountId 2 party2
    acc3 = AccountId 3 guarantor
