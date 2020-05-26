{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.CouponBond where

import Language.Marlowe.ACTUS.ActusContracts
import Language.Marlowe.ACTUS

import Data.Time
import Data.Time.Clock
import Data.Time.Clock.POSIX
import Data.Time.Clock.System

cb2 nm ied md notional rate = (emptyContractConfig ied)
    { maturityDate = Just md
    , notional = notional
    , nominalInterestRate = rate
    , interestPaymentCycle = Just $ Cycle nm Month LongLastStub
    , premiumDiscountAtIED = 0 }

couponBond numMonths =
  let td = fromGregorian 2020 5 14 in
  let tcb = cb2 numMonths td (addGregorianMonthsClip numMonths td) 1000 0.12 in
  genPrincialAtMaturnityContract "inverstor" "issuer" tcb

contract = couponBond 5

