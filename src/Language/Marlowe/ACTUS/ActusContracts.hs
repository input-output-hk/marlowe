{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Marlowe.ACTUS.ActusContracts where


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

import Language.Marlowe.ACTUS
import Language.Marlowe

dayToSlot :: Day -> Slot
dayToSlot d = let
    (MkSystemTime secs _) = utcToSystemTime (UTCTime d 0)
    in Slot (fromIntegral secs - cardanoEpochStart `mod` 20)

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


genPrincialAtMaturnityContract :: Party -> Party -> ContractConfig -> Contract
genPrincialAtMaturnityContract investor issuer config@ContractConfig{..} = let
    (f, _) = foldl generator (id, state) schedule
    in f Close
  where
    acc = AccountId 1 investor
    maturityDay = fromJust maturityDate
    maturitySlot = dayToSlot maturityDay
    state = pamStateInit initialExchangeDate maturityDay
    cs = pamContractSchedule config state
    scheduledEvents = eventScheduleByDay cs
    startDate = dayToSlot initialExchangeDate
    schedule = traceShow scheduledEvents $ Map.toList scheduledEvents

    generator (f, state) (day, events) =
        let (daysum, newState) = foldl
                (\(amount, st) event -> let
                    (amount', st') = pamPayoffAndStateTransition RPA config event day st
                    in (amount + amount', st'))
                (0, state) events
            from = if daysum <= 0 then investor else issuer
            to   = if daysum <= 0 then issuer else investor
            amount = abs daysum
            cont = if amount == 0 then id
                   else \contract -> f $ When [Case (Deposit acc from $ Constant amount)
                        (Pay acc (Party to) (Constant amount) contract)] (dayToSlot day) Close
            in (cont, newState)

genPrincialAtMaturnityGuaranteedContract :: Party -> Party -> Party ->  ContractConfig -> Contract
genPrincialAtMaturnityGuaranteedContract investor issuer guarantor config@ContractConfig{..} = guaranteed
  where
    cont = let (f, _) = foldl generator (id, state) schedule in f Close
    acc = AccountId 1 investor
    gacc = AccountId 2 guarantor
    maturityDay = fromJust maturityDate
    maturitySlot = dayToSlot maturityDay
    state = pamStateInit initialExchangeDate maturityDay
    cs = pamContractSchedule config state
    scheduledEvents = eventScheduleByDay cs
    startDate = dayToSlot initialExchangeDate
    schedule = traceShow (totalPayoff) $ Map.toList scheduledEvents
    totalPayoff = let
        (amount, _) = foldl (\(amount, st) (day, event) -> let
            (amount', st') = pamPayoffAndStateTransition RPA config event day st
            in (amount + if amount' > 0 then amount' else 0, st'))
            (0, state) (eventScheduleByDay1 cs)
        in amount

    guaranteed = When [Case (Deposit acc guarantor $ Constant totalPayoff) cont]
                startDate Close

    generator (f, state) (day, events) =
        let (daysum, newState) = foldl
                (\(amount, st) event -> let
                    (amount', st') = pamPayoffAndStateTransition RPA config event day st
                    in (amount + amount', st'))
                (0, state) events
            from = if daysum <= 0 then investor else issuer
            to   = if daysum <= 0 then issuer else investor
            amount = abs daysum
            cont = if amount == 0 then id
                    else \contract -> f $ When [Case (Deposit acc from $ Constant amount)
                        (Pay acc (Party to) (Constant amount)
                            (if from == investor then contract
                            else (Pay acc (Party guarantor) (Constant amount) contract)))]
                        (dayToSlot day) Close
            in (cont, newState)
