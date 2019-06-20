{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module ACTUS where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

{-
    = Data Dictionary

| SD    | StatusDate    |
| CNTRL | ContractRole
| LEICP | LegalEntityID Counterparty
| LEIRC | LegalEntityIDRecord Creator
| DS    | DeliverySettlement                |
| NT    | NotionalPrincipal                 |
| IPANX | CycleAnchorDateOfInterestPayment  |   Date from which the periodic occurring dates are calculated through the cycle length. The first IP event (first interest cash flow will be paid) takes place on this anchor. If IPANX is not set, then there will be exactly one interest cash flow at MaturityDate.
                                            |   Note: Interest accrual calculation starts always at IED (or PRD if set).
| IPCL  | CycleOfInterestPayment            |   For the explanation of the format see RRCL. The interval will be adjusted yet by EOMC and BDC.
                                                The lower boundary of accrual calculation is IED and the upper boundary MD where also a last interest cash flow happens. In case where the Cycle_Of_IP does not coincide with the Maturity_Date, the last interest cash flow will be time adjusted depending on the stub information.

PYTP PenaltyType Defines whether prepayment is linked to a penalty and of which kind.

    = State Variables

    = Contract Events

    A contract event e refers to any contractually scheduled or un-scheduled event at
a certain time t and of a certain type k.

    = State Transition Functions.

State Transition Functions (STF) define how the State Variables are being updated when a certain Contract Event e(k, t) applies from a pre-event (i.e. pre-time t) state indexed t− to a post-event (i.e. post-time t) state indexed t+.
The STF for an IP event and PAM contract is written as STF_IP_PAM() and maps e.g. state variable Nominal Accrued from a pre-event state Nact− to post-event state Nact+.

    = Contract Lifetime.

The lifetime of a contract starts with its SD and ends with
min(MD, AMD, PR∗, STD, TD, tmax).

    = Questions.

Unknowns: OPMO

-}

data ContractEvent  = IED  -- Initial Exchange Date Scheduled date of first principal event, start of accrual calculation
                    | IPCI -- Interest Capitalization Scheduled interest payment which is capitalized instead of paid out
                    | IP   -- Interest Payment Scheduled interest payment
                    | FP   -- Fee Payment Scheduled fee payment
                    | PR   -- Principal Redemption Scheduled principal redemption payment
                    | PI   -- Principal Increase Scheduled principal increase payments
                    | PRF  -- Principal Payment Amount Fixing Scheduled re-fixing of principal payment (PR or PI) amount
                    | PY   -- Penalty Payment Payment of a penalty (e.g. due to early repayment of principal outstanding)
                    | PP   -- Principal Prepayment Unscheduled (early) repayment of principal outstanding
                    | CD   -- Credit Default Credit event of counterparty to a contract
                    | RRF  -- Rate Reset Fixed Scheduled rate reset event where new rate is already fixed
                    | RR   -- Rate Reset Variable Scheduled rate reset event where new rate is fixed at event time
                    | DV   -- Dividend Payment Scheduled (e.g. announced) dividend payment
                    | PRD  -- Purchase Date Purchase date of a contract bought in the secondary market
                    | MR   -- Margin Call Date Scheduled margin call event
                    | TD   -- Termination Date Sell date of a contract sold in the secondary market
                    | SC   -- Scaling Index Revision Scheduled re-fixing of a scaling index
                    | IPCB -- Interest Payment Calculation Base Scheduled update to the calculation base for IP accruing
                    | XD   -- Execution Date Scheduled or unscheduled execution of e.g. an OPTNS or FUTUR contract
                    | STD  -- Settlement Date Date when payment for derivatives is settled
                    | MD   -- Maturity Date Scheduled maturity or expiry of a contract
                    | AD   -- Analysis Event Retrieves current contract states without alter these

-- CNTRL
data ContractRole   = RPA -- Real position asset
                    | RPL -- Real position liability
                    | CLO -- Role of a collateral
                    | CNO -- Role of a close-out-netting
                    | COL -- Role of an underlying to a collateral
                    | LG  -- Long position
                    | ST  -- Short position
                    | BUY -- Protection buyer
                    | SEL -- Protection seller
                    | RFL -- Receive first leg
                    | PFL -- Pay first leg
                    | RF  -- Receive fix leg
                    | PF  -- Pay fix leg

-- R
contractRoleSign :: ContractRole -> Integer
contractRoleSign role = case role of
    RPA ->  1
    RPL -> -1
    CLO ->  1
    CNO ->  1
    COL ->  1
    LG  ->  1
    ST  -> -1
    BUY ->  1
    SEL -> -1
    RFL ->  1
    PFL -> -1
    RF  ->  1
    PF  -> -1

-- | CS – Indicates different states of the contract from performance to default
data ContractStatus = PERF -- PF performant
                    | DL -- delayed
                    | DQ -- delinquent
                    | DF -- default

{-| Indicates whether the cash flows of the underlying financial contract of
    a combined contract are effectively exchanged or only used as
    a calculation base for the settlement cash flow(s).
-}
data DeliverySettlement = Delivery | Settlement

data FeeBasis = AbsoluteValue {- A -} | NotionalOfUnderlying {- N -}

data TimePeriod = Day | Week | Month | Quarter | HalfYear | Year
data Stub = LongLastStub | ShortLastStub
data Cycle = Cycle Integer TimePeriod Stub
data EndOfMonthConvention = EndOfMonth | SameDay
data BusinessDayConvention  = NoShift                           -- NULL
                            | ShiftCalculateFollowing           -- SCF
                            | ShiftCalculateModifiedFollowing   -- SCMF
                            | CalculateShiftFollowing           -- CSF
                            | CalculateShiftModifiedFollowing   -- CSMF
                            | ShiftCalculatePreceding           -- SCP
                            | ShiftCalculateModifiedFreceding   -- SCMP
                            | CalculateShiftPreceding           -- CSP
                            | CalculateShiftModifiedPreceding   -- CSMP


-- A schedule is a function S mapping times s, T with s < T and cycle c onto a sequence ~t of cyclic times
data Schedule = Schedule
    { scheduleStart :: Timeout
    , scheduleCycle :: Cycle
    , scheduleEnd   :: Timeout
    , scheduleEOMC  :: EndOfMonthConvention
    , scheduleBDC   :: BusinessDayConvention
    }

schedule :: Integer -> Schedule -> [Timeout]
schedule n Schedule{..} = [scheduleStart, scheduleEnd]
type Timeout = Integer
type Money = Integer

data PenaltyType    = NoPenalty {- O -}
                    | Absolute  {- A -}
                    | NominalRate   {- N -}
                    | CurrentInterestRateDifferential   {- I -}

{-| Contract Default Convention is a function D that maps the Prf state variable into
    +1 indicating that the contract is performing or 0 which reflext default and,
    from an analytical perspective, means that future cash flows cancel out
-}
contractDefaultConvention :: ContractStatus -> Integer
contractDefaultConvention PERF  = 1
contractDefaultConvention _     = 0

-- Year Fraction Convention
yearFractionConvention :: Timeout -> Timeout -> Double
yearFractionConvention = undefined

-- type LastEventDate = ContractEvent -> Timeout
type LastEventDate = Timeout

-- PAM: State Variables Initialization
data State = State
    { tmd :: Timeout        -- Maturity Date ?
    , nvl :: Money          -- Nominal Value. The outstanding nominal value
    , nv2 :: Money          -- Secondary Nominal Value. The outstanding nominal value of the second leg
    , nrt :: Money          -- Nominal Rate. The applicable nominal rate
    , nac :: Money          -- Nominal Accrued. The current value of nominal accrued interest at the Nominal Rate
    , fac :: Money          -- Fee Accrued?
    , icb :: Money          -- Interest Calculation Base. The basis at which interest is being accrued if different from Nvl
    , nsc :: Double         -- Notional Scaling Multiplier. The multiplier being applied to Notional/Principal related cashflows
    , isc :: Double         -- Interest Scaling Multiplier. The multiplier being applied to Interest related cash-flows
    , prf :: ContractStatus -- Contract performance
    , led :: LastEventDate        -- Last Event Date. The date of the most recent ContractEvent
    }

pamStateInit :: Timeout -> Timeout -> State
pamStateInit t0 maturityDate = State
    { tmd = maturityDate
    , nvl = 0
    , nv2 = 0
    , nrt = 0
    , nac = 0
    , fac = 0
    , icb = 0
    , nsc = 1.0
    , isc = 1.0
    , prf = PERF
    , led = t0
    }

type FeeRate = Double

data ContractConfig = ContractConfig
             { notional :: Money
             , premiumDiscountAtIED   :: Money
             , priceAtPurchaseDate    :: Money
             , priceAtTerminationDate :: Money
             , feeBasis :: FeeBasis
             , feeRate  :: FeeRate
             }

pamPayoff :: ContractRole
    -> ContractConfig
    -> Timeout
    -> ContractEvent
    -> State
    -> Money
pamPayoff role ContractConfig{..} currTime event State{..} =
  case event of
    IED     ->  -- D(Prft− )R(CNTRL)(−1)(NT + PDIED)
                dperf * rsign * (-1) * (notional + premiumDiscountAtIED)
    IPCI    -> 0
    IP      -> dperf * round (isc * fromIntegral (nac + round (yearFrac led currTime * fromIntegral nrt) * nvl))
                -- D(Prft− )Isct− (Nact− + Y (Ledt− , t)Nrtt− Nvlt− )
    FP      ->  let c = fromIntegral (dperf * rsign) * feeRate
                in case feeBasis of
                    AbsoluteValue -> round c
                    NotionalOfUnderlying -> round (c * yearFrac led currTime * fromIntegral nvl) + fac

    PR      ->  -- D(Prft− )Nsct− Nvlt−
                round (fromIntegral (dperf * nvl) * nsc)
    PI      -> undefined
    PRF     -> undefined
    PY      -> 0 -- todo
    PP      -> 0 -- D(Prft− )Orf (OPMO, t) -- todo
    CD      -> 0
    RRF     -> 0
    RR      -> 0
    DV      -> undefined
    PRD     -> dperf * rsign * (-1) * (priceAtPurchaseDate + nac + round (yearFrac led currTime * fromIntegral nrt * fromIntegral nvl))
                -- D(Prft− )R(CNTRL)(−1)(PPRD + Nact− +Y (Ledt− , t)Nrtt− Nvlt− )
    MR      -> undefined
    TD      -> dperf * rsign * (priceAtTerminationDate + nac + round (yearFrac led currTime * fromIntegral nrt * fromIntegral nvl))
                -- D(Prft− )R(CNTRL)(PTD + Nact− + Y (Ledt− , t)Nrtt− Nvlt− )
    SC      -> 0
    IPCB    -> undefined
    XD      -> undefined
    STD     -> undefined
    MD      -> undefined
    AD      -> 0
  where dperf = contractDefaultConvention prf
        rsign = contractRoleSign role
        yearFrac a b = yearFractionConvention a b



pamStateTransition :: ContractRole
    -> ContractConfig
    -> ContractEvent
    -> Timeout
    -> State
    -> State
pamStateTransition role ContractConfig{..} event currTime state@State{..} = case event of
    IED     -> state { nvl = rsign * notional
                     , nrt = 0 -- todo
                     , nac = 0 -- todo
                     , led = currTime
                     }
    IPCI    -> state { nvl = nvl + nac + yearNrtNvl
                     , nac = 0
                     , fac = newFac
                     , led = currTime
                     }
    IP      -> state { nac = 0
                     , fac = newFac
                     , led = currTime
                     }
    FP      -> state { nac = nac + yearNrtNvl
                     , fac = 0
                     , led = currTime
                     }
    PR      -> state { nvl = 0
                     , nrt = 0
                     , led = currTime
                     }
    PI      -> undefined
    PRF     -> undefined
    PY      -> state { nac = nac + yearNrtNvl
                     , fac = newFac
                     , led = currTime
                     }
    PP      -> state { nac = nac + yearNrtNvl
                     , fac = newFac
                     , led = currTime
                     }
    CD      -> state { nac = nac + yearNrtNvl
                     , fac = newFac
                     , led = currTime
                     }
    RRF     -> state { nac = nac + yearNrtNvl
                     , fac = newFac
                     , prf = DF
                     , led = currTime
                     }
    RR      -> state { nac = nac + yearNrtNvl
                     , fac = newFac
                     , nrt = nrt -- todo
                     , led = currTime
                     }
    DV      -> undefined
    PRD     -> state { nac = nac + yearNrtNvl
                     , fac = newFac
                     , led = currTime
                     }
    MR      -> undefined
    TD      -> state { nvl = 0
                     , nac = 0
                     , fac = 0
                     , nrt = 0
                     , led = currTime
                     }
    SC      -> state { nac = nac + yearNrtNvl
                     , fac = newFac
                     , nsc = nsc -- todo
                     , isc = isc -- todo
                     , led = currTime
                     }
    IPCB    -> undefined
    XD      -> undefined
    STD     -> undefined
    MD      -> undefined
    AD      -> state { nac = nac + yearNrtNvl
                     , led = currTime
                     }
                -- Nact+ = Nact− + Y (Ledt−1, t)Nrtt− Nvlt−; Ledt+ = t
  where dperf = contractDefaultConvention prf
        rsign = contractRoleSign role
        yearFrac a b = yearFractionConvention a b
        yearNvl = yearFrac led currTime * fromIntegral nvl
        yearNrtNvl = round (yearFrac led currTime * fromIntegral (nrt * nvl))
        newFac = case feeBasis of
            AbsoluteValue -> round feeRate -- todo
            NotionalOfUnderlying -> fac + round (yearNvl * feeRate)
