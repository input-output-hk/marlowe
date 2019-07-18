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
    , interestPaymentCycle = Just $ Cycle 6 Month LongLastStub
    , premiumDiscountAtIED = 0 }


genCouponBondContract :: Party -> Party -> ContractConfig -> Contract
genCouponBondContract investor issuer config@ContractConfig{..} = let
    (f, _) = foldl generator (id, state) sch
    in f RefundAll
  where
    acc = AccountId 1 investor
    maturityDay = fromJust maturityDate
    maturitySlot :: Integer
    maturitySlot = dayToSlot maturityDay
    state = (pamStateInit initialExchangeDate maturityDay) { nvl = notional, nrt = nominalInterestRate }
    cs = contractSchedule config state
    schedule = eventScheduleByDay $ traceShow cs cs
    startDate = dayToSlot initialExchangeDate
    sch = traceShow schedule $ Map.toList schedule

    genEventAmount state day event = case event of
        IED -> (pamPayoff RPA config day IED state, pamStateTransition RPA config event day state)
        IP  -> (pamPayoff RPA config day IP state,  pamStateTransition RPA config event day state)
        PR  -> (pamPayoff RPA config day PR state,  pamStateTransition RPA config event day state)
        MD  -> (notional, state)
        _ -> error $ "Unexpected " ++ show event

    generator (f, state) (day, events) =
        let (daysum, newState) = foldl
                (\(am, st) ev -> let (am', st') = genEventAmount st day ev in (am + am', st'))
                (0, state) events
            from = if daysum <= 0 then investor else issuer
            to   = if daysum <= 0 then issuer else investor
            amount = abs daysum
        in (\contract -> f $ When [Case (Deposit acc from $ Constant amount)
                    (Pay acc (Party to) (Constant amount) contract)]
                (dayToSlot day) RefundAll, newState)
