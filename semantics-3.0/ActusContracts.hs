{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module ActusContracts where


import Data.Maybe
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Time
import Data.Time.Clock
import Data.Time.Clock.POSIX
import Data.Time.Clock.System
import Debug.Trace

import ACTUS
import Semantics4

zcb ied md notional discount = (emptyContractConfig ied)
    { maturityDate = Just md
    , notional = notional
    , premiumDiscountAtIED = discount }

cb ied md notional rate = (emptyContractConfig ied)
    { maturityDate = Just md
    , notional = notional
    , nominalInterestRate = rate
    , interestPaymentCycle = Just $ Cycle 3 Month LongLastStub
    , premiumDiscountAtIED = 0 }


genCouponBondContract :: Party -> Party -> ContractConfig -> Contract
genCouponBondContract investor issuer config@ContractConfig{..} = foldr generator RefundAll sch
  where
    acc = AccountId 1 investor
    maturityDay = fromJust maturityDate
    maturitySlot :: Integer
    maturitySlot = dayToSlot maturityDay
    state = (pamStateInit initialExchangeDate maturityDay) { nvl = notional, nrt = nominalInterestRate }
    cs = contractSchedule config state
    schedule = eventScheduleByDay $ traceShow cs cs
    startDate = dayToSlot initialExchangeDate
    sch = Map.toList schedule

    genEventAmount day event = case event of
        IED -> pamPayoff RPA config day IED state
        IP  -> 20 -- pamPayoff RPA config day IP state
        PR  -> pamPayoff RPA config day PR state
        MD  -> 0
        _ -> error $ "Unexpected " ++ (show event)


    generator (day, events) contract =
        let daysum = sum $ fmap (genEventAmount day) events
            from = if daysum <= 0 then investor else issuer
            to   = if daysum <= 0 then issuer else investor
            amount = abs daysum
        in When [Case (Deposit acc from $ Constant amount)
                    (Pay acc (Party to) (Constant acc) contract)]
                (dayToSlot day) RefundAll
