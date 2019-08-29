{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Marlowe.Analysis.FSSemantics where

import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Set        (Set)
import qualified Data.Set        as S
import           Data.SBV
import qualified Data.SBV.Tuple as ST
import qualified Data.SBV.Either as SE
import qualified Data.SBV.Maybe as SM
import qualified Data.SBV.List as SL
import qualified Language.Marlowe.Analysis.FSMap as FSMap
import           Language.Marlowe.Analysis.FSMap(FSMap, NMap)
import qualified Language.Marlowe.Analysis.FSSet as FSSet
import           Language.Marlowe.Analysis.FSSet(FSSet, NSet)
import           Language.Marlowe.Analysis.Numbering
import           Language.Marlowe.Analysis.MkSymb(mkSymbolicDatatype)
import qualified Language.Marlowe.Semantics as MS

type SlotNumber = Integer
type SSlotNumber = SInteger
type SlotInterval = (SlotNumber, SlotNumber)
type SSlotInterval = STuple SlotNumber SlotNumber
type PubKey = Integer

type Party = PubKey
type SParty = SBV PubKey

type NumChoice = Integer
type NumAccount = Integer
type STimeout = SSlotNumber
type Timeout = SlotNumber

type Money = Integer
type SMoney = SInteger

type ChosenNum = Integer
type SChosenNum = SBV ChosenNum

data AccountId = AccountId NumAccount Party
  deriving (Eq,Ord,Show,Read)
type NAccountId = (NumAccount, Party)
type SAccountId = STuple NumAccount Party

sAccountId :: NumAccount -> Party -> SAccountId
sAccountId a p = ST.tuple (literal a, literal p)

nestAccountId :: AccountId -> NAccountId
nestAccountId (AccountId numAccId party) = (numAccId, party)

literalAccountId :: AccountId -> SAccountId
literalAccountId (AccountId a p) = sAccountId a p

nestedToSAccountId :: NAccountId -> SAccountId
nestedToSAccountId (a, p) = sAccountId a p

accountOwner :: AccountId -> Party
accountOwner (AccountId _ party) = party

symAccountOwner :: SAccountId -> SParty
symAccountOwner x = party
  where (numAcc, party) = ST.untuple x

data ChoiceId = ChoiceId NumChoice Party
  deriving (Eq,Ord,Show,Read)
type NChoiceId = (NumChoice, Party)
type SChoiceId = STuple NumChoice Party

sChoiceId :: NumChoice -> Party -> SChoiceId
sChoiceId c p = ST.tuple (literal c, literal p)

literalChoiceId :: ChoiceId -> SChoiceId
literalChoiceId (ChoiceId c p) = sChoiceId c p

newtype OracleId = OracleId PubKey
  deriving (Eq,Ord,Show,Read)

newtype ValueId = ValueId Integer
  deriving (Eq,Ord,Show,Read)
type NValueId = Integer
type SValueId = SInteger

literalValueId :: ValueId -> SValueId
literalValueId (ValueId x) = literal x

data Value = AvailableMoney AccountId
           | Constant Integer
           | NegValue Value
           | AddValue Value Value
           | SubValue Value Value
           | ChoiceValue ChoiceId Value
           | SlotIntervalStart
           | SlotIntervalEnd
           | UseValue ValueId
--           | OracleValue OracleId Value
  deriving (Eq,Ord,Show,Read)

data Observation = AndObs Observation Observation
                 | OrObs Observation Observation
                 | NotObs Observation
                 | ChoseSomething ChoiceId
                 | ValueGE Value Value
                 | ValueGT Value Value
                 | ValueLT Value Value
                 | ValueLE Value Value
                 | ValueEQ Value Value
                 | TrueObs
                 | FalseObs
--                 | OracleValueProvided OracleId
  deriving (Eq,Ord,Show,Read)

type Bound = (Integer, Integer)

inBounds :: SChosenNum -> [Bound] -> SBool
inBounds num = foldl' (\acc (l, u) -> acc .|| ((num .>= literal l) .&& (num .<= literal u)))
                      sFalse

data Action = Deposit AccountId Party Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving (Eq,Ord,Show,Read)

data Payee = Account NAccountId
           | Party Party
  deriving (Eq,Ord,Show,Read)

mkSymbolicDatatype ''Payee

data Case = Case Action Contract
  deriving (Eq,Ord,Show,Read)

data Contract = Refund
              | Pay AccountId Payee Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract
              | Let ValueId Value Contract
  deriving (Eq,Ord,Show,Read)

--data State = State { account :: Map AccountId Money
--                   , choice  :: Map ChoiceId ChosenNum
--                   , boundValues :: Map ValueId Integer
--                   , minSlot :: SSlotNumber }
type SState = STuple4 (NMap NAccountId Money)
                      (NMap NChoiceId ChosenNum)
                      (NMap NValueId Integer)
                      SlotNumber
type State = ( NMap NAccountId Money
             , NMap NChoiceId ChosenNum
             , NMap NValueId Integer
             , SlotNumber)

emptySState :: SSlotNumber -> SState
emptySState sn = ST.tuple (FSMap.empty, FSMap.empty, FSMap.empty, sn)

setAccount :: SState -> SBV [(NAccountId, Money)] -> SState
setAccount t ac = let (_, ch, va, sl) = ST.untuple t in
                  ST.tuple (ac, ch, va, sl)

setChoice :: SState -> FSMap NChoiceId ChosenNum -> SState
setChoice t ch = let (ac, _, va, sl) = ST.untuple t in
                     ST.tuple (ac, ch, va, sl)

setBoundValues :: SState -> FSMap NValueId Integer -> SState
setBoundValues t va = let (ac, ch, _, sl) = ST.untuple t in
                      ST.tuple (ac, ch, va, sl)

account :: SState -> FSMap NAccountId Money
account st = ac
  where (ac, _, _, _) = ST.untuple st

choice :: SState -> FSMap NChoiceId ChosenNum
choice st = cho
  where (_, cho, _, _) = ST.untuple st

boundValues :: SState -> FSMap NValueId Integer
boundValues st = bv
  where (_, _, bv, _) = ST.untuple st

minSlot :: SState -> SSlotNumber
minSlot st = ms
  where (_, _, _, ms) = ST.untuple st

setMinSlot :: SState -> SSlotNumber -> SState
setMinSlot st nms = ST.tuple (ac, cho, bv, nms)
  where (ac, cho, bv, _) = ST.untuple st

--data Environment = Environment { slotInterval :: SlotInterval }
type Environment = SlotInterval
type SEnvironment = SSlotInterval

slotInterval :: SEnvironment -> SSlotInterval
slotInterval = id

setSlotInterval :: SEnvironment -> SSlotInterval -> SEnvironment
setSlotInterval _ si = si

sEnvironment :: SSlotInterval -> SEnvironment
sEnvironment si = si

--type SInput = SMaybe (SEither (AccountId, Party, Money) (ChoiceId, ChosenNum))
data Input = IDeposit NAccountId Party Money
           | IChoice NChoiceId ChosenNum
           | INotify
  deriving (Eq,Ord,Show,Read)

mkSymbolicDatatype ''Input

data Bounds = Bounds { numParties :: Integer
                     , numChoices :: Integer
                     , numAccounts :: Integer
                     , numLets :: Integer
                     , numActions :: Integer
                     }

-- TRANSACTION OUTCOMES

type STransactionOutcomes = FSMap Party Money
type NTransactionOutcomes = NMap Party Money

emptyOutcome :: STransactionOutcomes
emptyOutcome = FSMap.empty

isEmptyOutcome :: Bounds -> STransactionOutcomes -> SBool
isEmptyOutcome bnds trOut = FSMap.all (numParties bnds) (.== 0) trOut

-- Adds a value to the map of outcomes
addOutcome :: Bounds -> SParty -> SMoney -> STransactionOutcomes -> STransactionOutcomes
addOutcome bnds party diffValue trOut =
    FSMap.insert (numParties bnds) party newValue trOut
  where
    newValue = (SM.fromMaybe 0 (FSMap.lookup (numParties bnds) party trOut)) + diffValue

-- Add two transaction outcomes together
combineOutcomes :: Bounds -> STransactionOutcomes -> STransactionOutcomes
                -> STransactionOutcomes
combineOutcomes bnds = FSMap.unionWith (numParties bnds) (+)

-- INTERVALS

-- Processing of slot interval
data IntervalError = InvalidInterval SlotInterval
                   | IntervalInPastError SlotNumber SlotInterval
  deriving (Eq,Show)

mkSymbolicDatatype ''IntervalError

data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError NIntervalError
  deriving (Eq,Show)

mkSymbolicDatatype ''IntervalResult

fixInterval :: SSlotInterval -> SState -> SIntervalResult
fixInterval i st =
  ite (h .< l)
      (sIntervalError $ sInvalidInterval i)
      (ite (h .< minSlotV)
           (sIntervalError $ sIntervalInPastError minSlotV i)
           (sIntervalTrimmed env nst))
  where
    (l, h) = ST.untuple i
    minSlotV = minSlot st
    nl = smax l minSlotV
    tInt = ST.tuple (nl, h)
    env = sEnvironment tInt
    nst = st `setMinSlot` nl

-- EVALUATION

-- Evaluate a value
evalValue :: Bounds -> SEnvironment -> SState -> Value -> SInteger
evalValue bnds env state value =
  case value of
    AvailableMoney (AccountId a p) -> FSMap.findWithDefault (numAccounts bnds)
                                                            0 (sAccountId a p) $
                                                            account state
    Constant integer         -> literal integer
    NegValue val             -> go val
    AddValue lhs rhs         -> go lhs + go rhs
    SubValue lhs rhs         -> go lhs + go rhs
    ChoiceValue (ChoiceId c p) defVal -> FSMap.findWithDefault (numChoices bnds)
                                                               (go defVal)
                                                               (sChoiceId c p) $
                                                               choice state
    SlotIntervalStart        -> inStart
    SlotIntervalEnd          -> inEnd
    UseValue (ValueId valId) -> FSMap.findWithDefault (numLets bnds)
                                                      0 (literal valId) $
                                                      boundValues state
  where go = evalValue bnds env state
        (inStart, inEnd) = ST.untuple $ slotInterval env

-- Evaluate an observation
evalObservation :: Bounds -> SEnvironment -> SState -> Observation -> SBool
evalObservation bnds env state obs =
  case obs of
    AndObs lhs rhs       -> goObs lhs .&& goObs rhs
    OrObs lhs rhs        -> goObs lhs .|| goObs rhs
    NotObs subObs        -> sNot $ goObs subObs
    ChoseSomething (ChoiceId c p) -> FSMap.member (numChoices bnds)
                                                  (sChoiceId c p) $
                                                  choice state
    ValueGE lhs rhs      -> goVal lhs .>= goVal rhs
    ValueGT lhs rhs      -> goVal lhs .> goVal rhs
    ValueLT lhs rhs      -> goVal lhs .< goVal rhs
    ValueLE lhs rhs      -> goVal lhs .<= goVal rhs
    ValueEQ lhs rhs      -> goVal lhs .== goVal rhs
    TrueObs              -> sTrue
    FalseObs             -> sFalse
  where
    goObs = evalObservation bnds env state
    goVal = evalValue bnds env state

-- Pick the first account with money in it
refundOne :: Integer -> FSMap NAccountId Money
          -> SMaybe ((Party, Money), NMap NAccountId Money)
refundOne iters accounts
  | iters >= 0 =
      SM.maybe SM.sNothing
               (\ tup ->
                    let (he, rest) = ST.untuple tup in
                    let (accId, mon) = ST.untuple he in
                    ite (mon .> (literal 0))
                        (SM.sJust $ ST.tuple ( ST.tuple (symAccountOwner accId, mon)
                                             , rest))
                        (refundOne (iters - 1) rest))
               (FSMap.minViewWithKey accounts)
  | otherwise = SM.sNothing

-- Obtains the amount of money available an account
moneyInAccount :: Integer -> FSMap NAccountId Money -> SAccountId -> SMoney
moneyInAccount iters accs accId = FSMap.findWithDefault iters 0 accId accs

-- Sets the amount of money available in an account
updateMoneyInAccount :: Integer -> FSMap NAccountId Money -> SAccountId -> SMoney
                     -> FSMap NAccountId Money
updateMoneyInAccount iters accs accId mon =
  ite (mon .<= 0)
      (FSMap.delete iters accId accs)
      (FSMap.insert iters accId mon accs)

-- Withdraw up to the given amount of money from an account
-- Return the amount of money withdrawn
withdrawMoneyFromAccount :: Bounds -> FSMap NAccountId Money -> SAccountId -> SMoney
                         -> STuple Money (NMap NAccountId Money)
withdrawMoneyFromAccount bnds accs accId mon = ST.tuple (withdrawnMoney, newAcc)
  where
    naccs = numAccounts bnds
    avMoney = moneyInAccount naccs accs accId
    withdrawnMoney = smin avMoney mon
    newAvMoney = avMoney - withdrawnMoney
    newAcc = updateMoneyInAccount naccs accs accId newAvMoney

-- Add the given amount of money to an accoun (only if it is positive)
-- Return the updated Map
addMoneyToAccount :: Bounds -> FSMap NAccountId Money -> SAccountId -> SMoney
                  -> FSMap NAccountId Money
addMoneyToAccount bnds accs accId mon =
  ite (mon .<= 0)
      accs
      (updateMoneyInAccount naccs accs accId newAvMoney)
  where
    naccs = numAccounts bnds
    avMoney = moneyInAccount naccs accs accId
    newAvMoney = avMoney + mon

data ReduceEffect = ReduceNoEffect
                  | ReduceNormalPay Party Money
  deriving (Eq,Ord,Show,Read)

mkSymbolicDatatype ''ReduceEffect

-- Gives the given amount of money to the given payee
-- Return the appropriate effect and updated Map
giveMoney :: Bounds -> FSMap NAccountId Money -> Payee -> SMoney
          -> STuple2 NReduceEffect (NMap NAccountId Money)
giveMoney bnds accs (Party party) mon = ST.tuple ( sReduceNormalPay (literal party) mon
                                                 , accs )
giveMoney bnds accs (Account accId) mon = ST.tuple ( sReduceNoEffect
                                                   , newAccs )
    where newAccs = addMoneyToAccount bnds accs (nestedToSAccountId accId) mon


-- REDUCE

data ReduceWarning = ReduceNoWarning
                   | ReduceNonPositivePay NAccountId NPayee Money
                   | ReducePartialPay NAccountId NPayee Money Money
                                    -- ^ src    ^ dest ^ paid ^ expected
                   | ReduceShadowing NValueId Integer Integer
                                     -- oldVal ^  newVal ^
  deriving (Eq,Ord,Show,Read)

mkSymbolicDatatype ''ReduceWarning

data ReduceError = ReduceAmbiguousSlotInterval
  deriving (Eq,Ord,Show,Read)

mkSymbolicDatatype ''ReduceError

data ReduceResult = Reduced NReduceWarning NReduceEffect State
                  | NotReduced
                  | ReduceError NReduceError
  deriving (Eq,Show)

mkSymbolicDatatype ''ReduceResult

data DetReduceResult = DRRContractOver
                     | DRRRefundStage
                     | DRRNoProgressNormal
                     | DRRNoProgressError
                     | DRRProgress Contract Integer -- Integer is num of Payments
  deriving (Eq,Ord,Show,Read)

-- Carry a step of the contract with no inputs
reduce :: SymVal a => Bounds -> SEnvironment -> SState -> Contract
       -> (SReduceResult -> DetReduceResult -> SBV a) -> SBV a
reduce bnds _ state c@Refund f =
  SM.maybe (f sNotReduced $ DRRContractOver)
           (\justTup -> let (pm, newAccount) = ST.untuple justTup in
                        let (party, money) = ST.untuple pm in
                        let newState = state `setAccount` newAccount in
                        (f (sReduced sReduceNoWarning
                                     (sReduceNormalPay party money)
                                     newState)
                           DRRRefundStage))
           (refundOne (numAccounts bnds) $ account state)
reduce bnds env state c@(Pay accId payee val nc) f =
  ite (mon .<= 0)
      (f (sReduced (sReduceNonPositivePay (literalAccountId accId)
                                          (literal $ nestPayee payee)
                                          mon)
                   sReduceNoEffect state)
         (DRRProgress nc 0))
      (f (sReduced noMonWarn payEffect (state `setAccount` finalAccs)) (DRRProgress nc 1))
  where mon = evalValue bnds env state val
        (paidMon, newAccs) = ST.untuple $
                               withdrawMoneyFromAccount bnds (account state)
                                                        (literalAccountId accId) mon
        noMonWarn = ite (paidMon .< mon)
                        (sReducePartialPay (literalAccountId accId)
                                           (literal $ nestPayee payee) paidMon mon)
                        (sReduceNoWarning)
        (payEffect, finalAccs) = ST.untuple $ giveMoney bnds newAccs payee paidMon
reduce bnds env state (If obs cont1 cont2) f =
  ite (evalObservation bnds env state obs)
      (f (sReduced sReduceNoWarning sReduceNoEffect state) (DRRProgress cont1 0))
      (f (sReduced sReduceNoWarning sReduceNoEffect state) (DRRProgress cont2 0))
reduce bnds env state (When _ timeout c) f =
   ite (endSlot .< (literal timeout))
       (f sNotReduced DRRNoProgressNormal)
       (ite (startSlot .>= (literal timeout))
            (f (sReduced sReduceNoWarning sReduceNoEffect state) $ DRRProgress c 0)
            (f (sReduceError sReduceAmbiguousSlotInterval) $ DRRNoProgressError))
  where (startSlot, endSlot) = ST.untuple $ slotInterval env
reduce bnds env state (Let valId val cont) f =
    f (sReduced warn sReduceNoEffect ns) (DRRProgress cont 0)
  where
    sv = boundValues state
    evVal = evalValue bnds env state val
    nsv = FSMap.insert (numLets bnds) lValId evVal sv
    ns = state `setBoundValues` nsv
    warn = SM.maybe (sReduceNoWarning)
                    (\oldVal -> sReduceShadowing lValId oldVal evVal)
                    (FSMap.lookup (numLets bnds) lValId sv)
    lValId = literalValueId valId

-- REDUCE ALL

data ReduceAllResult = ReducedAll [NReduceWarning] [NReduceEffect] State
                     | ReduceAllError NReduceError
  deriving (Eq,Show)

mkSymbolicDatatype ''ReduceAllResult

data DetReduceAllResult = DRARContractOver
                        | DRARError
                        | DRARNormal Contract Integer -- Integer is num of Payments
  deriving (Eq,Ord,Show,Read)

-- Reduce until it cannot be reduced more

splitReduceResultRefund :: SList NReduceWarning -> SList NReduceEffect -> SSReduceResult
                        -> (SList NReduceWarning, SList NReduceEffect, SState)
splitReduceResultRefund wa ef (SSReduced twa tef tsta) =
  ( symCaseReduceWarning
     (\x -> case x of -- Do not add if ReduceNoWarning
              SSReduceNoWarning -> wa
              _ -> twa SL..: wa) twa
  , symCaseReduceEffect
     (\x -> case x of -- Do not add if ReduceNoEffect
              SSReduceNoEffect -> ef
              _ -> tef SL..: ef) tef
  , tsta)
splitReduceResultRefund _ _ SSNotReduced = ([], [], emptySState 0) -- SNH
splitReduceResultRefund _ _ (SSReduceError _) = ([], [], emptySState 0) -- SNH 

splitReduceResultReduce :: SList NReduceWarning -> SList NReduceEffect -> SSReduceResult
                        -> (SList NReduceWarning, SList NReduceEffect, SState,
                            SReduceError)
splitReduceResultReduce wa ef (SSReduced twa tef tsta) = 
  ( symCaseReduceWarning
       (\x -> case x of -- Do not add if ReduceNoWarning
                SSReduceNoWarning -> wa
                _ -> twa SL..: wa) twa
  , symCaseReduceEffect
       (\x -> case x of -- Do not add if ReduceNoEffect
                SSReduceNoEffect -> ef
                _ -> tef SL..: ef) tef
  , tsta
  , sReduceAmbiguousSlotInterval {- SNH -}) 
splitReduceResultReduce _ _ SSNotReduced =
  ([] {- SNH -}, [] {- SNH -}, emptySState 0 {- SNH -}, sReduceAmbiguousSlotInterval {- SNH -})
splitReduceResultReduce _ _ (SSReduceError terr) = ([] {- SNH -}, [] {- SNH -}, emptySState 0{- SNH -}, terr)

reduceAllAux :: SymVal a => Bounds -> Integer -> Maybe Integer -> SEnvironment
             -> SState -> Contract -> SList NReduceWarning -> SList NReduceEffect
             -> (SReduceAllResult -> DetReduceAllResult -> SBV a) -> SBV a
reduceAllAux bnds payNum (Just x) env sta c wa ef f
  | x >= 0 = reduce bnds env sta c contFunc
  | otherwise = f (sReducedAll wa ef sta) DRARContractOver
  where contFunc sr dr =
          (let (nwa, nef, nsta) =
                 ST.untuple ((symCaseReduceResult
                                (ST.tuple . (splitReduceResultRefund wa ef))) sr) in
          case dr of
            DRRContractOver -> f (sReducedAll wa ef sta) DRARContractOver
            DRRRefundStage -> reduceAllAux bnds (payNum + 1) (Just (x - 1))
                                             env nsta c nwa nef f
            DRRNoProgressNormal -> f (sReduceAllError sReduceAmbiguousSlotInterval) DRARError -- SNH 
            DRRNoProgressError -> f (sReduceAllError sReduceAmbiguousSlotInterval) DRARError --SNH
            DRRProgress _ _ -> f (sReduceAllError sReduceAmbiguousSlotInterval) DRARError) --SNH 
reduceAllAux bnds payNum Nothing env sta c wa ef f =
    reduce bnds env sta c contFunc
  where contFunc sr dr =
          (let (nwa, nef, nsta, err) =
                 ST.untuple ((symCaseReduceResult
                                (ST.tuple . (splitReduceResultReduce wa ef))) sr) in
          case dr of
            DRRContractOver -> f (sReducedAll wa ef sta) DRARContractOver
            DRRRefundStage -> reduceAllAux bnds (payNum + 1) (Just $ numAccounts bnds)
                                           env nsta c nwa nef f
            DRRNoProgressNormal -> f (sReducedAll wa ef sta) $ DRARNormal c 0
            DRRNoProgressError -> f (sReduceAllError err) DRARError
            DRRProgress nc p -> reduceAllAux bnds (payNum + p) Nothing env nsta nc nwa nef f)

reduceAll :: SymVal a => Bounds -> SEnvironment -> SState -> Contract
          -> (SReduceAllResult -> DetReduceAllResult -> SBV a) -> SBV a
reduceAll bnds env sta c f = reduceAllAux bnds 0 Nothing env sta c [] [] f

splitReduceAllResult :: SList NReduceWarning -> SList NReduceEffect -> SSReduceAllResult
                     -> SBV ([NReduceWarning], [NReduceEffect], State, NReduceError)
splitReduceAllResult wa ef (SSReducedAll twa tef tsta) = ST.tuple $
  (twa SL..++ wa, tef SL..++ ef, tsta, sReduceAmbiguousSlotInterval {- SNH -}) 
splitReduceAllResult _ _ (SSReduceAllError terr) =
   ST.tuple $ ([] {- SNH -}, [] {- SNH -}, emptySState 0{- SNH -}, terr)

splitReduceAllResultWrap :: SList NReduceWarning -> SList NReduceEffect -> SReduceAllResult
                         -> SBV ([NReduceWarning], [NReduceEffect], State, NReduceError)
splitReduceAllResultWrap wa ef sr = symCaseReduceAllResult (splitReduceAllResult wa ef) sr


-- APPLY

data ApplyError = ApplyNoMatch
  deriving (Eq,Ord,Show,Read)

mkSymbolicDatatype ''ApplyError

data ApplyResult = Applied State
                 | ApplyError NApplyError
  deriving (Eq,Show)

mkSymbolicDatatype ''ApplyResult

data DetApplyResult = DARNormal Contract
                                Integer -- num of Inputs
                    | DARError

-- Apply a single Input to the contract (assumes the contract is reduced)
applyCases :: SymVal a => Bounds -> SEnvironment -> SState -> SSInput -> [Case] ->
              (SApplyResult -> DetApplyResult -> SBV a) -> SBV a
applyCases bnds env state inp@(SSIDeposit accId1 party1 mon1)
           ((Case (Deposit accId2 party2 val2) nc): t) f =
  ite ((accId1 .== sAccId2) .&& (party1 .== sParty2) .&& (mon1 .== mon2))
      (f (sApplied newState) (DARNormal nc 1))
      (applyCases bnds env state inp t f)
  where sAccId2 = literalAccountId accId2
        sParty2 = literal party2
        mon2 = evalValue bnds env state val2
        accs = account state
        newAccs = addMoneyToAccount bnds accs accId1 mon1
        newState = state `setAccount` newAccs
applyCases bnds env state inp@(SSIChoice choId1 cho1)
           (Case (Choice choId2 bounds2) nc : t) f =
  ite ((choId1 .== sChoId2) .&& (inBounds cho1 bounds2))
      (f (sApplied newState) (DARNormal nc 0))
      (applyCases bnds env state inp t f)
  where newState = state `setChoice`
                     (FSMap.insert (numChoices bnds) choId1 cho1 $ choice state)
        sChoId2 = literalChoiceId choId2
applyCases bnds env state SSINotify (Case (Notify obs) nc : t) f =
  (f (sApplied state) (DARNormal nc 0))
applyCases _ _ _ _ _ f = f (sApplyError sApplyNoMatch) DARError

apply :: SymVal a => Bounds -> SEnvironment -> SState -> SInput -> Contract ->
         (SApplyResult -> DetApplyResult -> SBV a) -> SBV a
apply bnds env state act (When cases _ _ ) f =
  symCaseInput (\x -> applyCases bnds env state x cases f) act
apply _ _ _ _ _ f = f (sApplyError sApplyNoMatch) DARError

-- APPLY ALL

data ApplyAllResult = AppliedAll [NReduceWarning] [NReduceEffect] State
                    | AAApplyError NApplyError
                    | AAReduceError NReduceError
  deriving (Eq,Show)

mkSymbolicDatatype ''ApplyAllResult

data DetApplyAllResult = DAARNormal Contract
                                    Integer -- num of Payments
                                    Integer -- num of Inputs 
                       | DAARError


-- Apply a list of Inputs to the contract
applyAllAux :: SymVal a => Integer
            -> Bounds -> Integer -> Integer
            -> SEnvironment -> SState -> Contract -> SList NInput
            -> SList NReduceWarning -> SList NReduceEffect
            -> (SApplyAllResult -> DetApplyAllResult -> SBV a) -> SBV a
applyAllAux n bnds numPays numInps env state c l wa ef f
  | n >= 0 = reduceAll bnds env state c contFunReduce
  | otherwise = f (sAAReduceError sReduceAmbiguousSlotInterval) DAARError -- SNH
  where contFunReduce sr DRARError =
          let (_, _, _, err) = ST.untuple $ splitReduceAllResultWrap wa ef sr in
          (f (sAAApplyError err) DAARError)
        contFunReduce sr DRARContractOver =
          let (nwa, nef, nstate, _) = ST.untuple $ splitReduceAllResultWrap wa ef sr in
          ite (SL.null l)
              (f (sAppliedAll nwa nef nstate) $ DAARNormal Refund numPays numInps)
              (f (sAAApplyError sApplyNoMatch) DAARError)
        contFunReduce sr (DRARNormal nc p) =
          let (nwa, nef, nstate, _) = ST.untuple $ splitReduceAllResultWrap wa ef sr in
          ite (SL.null l)
              (f (sAppliedAll nwa nef nstate) $ DAARNormal nc (p + numPays) numInps)
              (apply bnds env nstate (SL.head l) nc (contFunApply (SL.tail l) nwa nef p))
        contFunApply t nwa nef np sr DARError =
          f (symCaseApplyResult
               (\x -> case x of
                        SSApplied _ -> sAAReduceError sReduceAmbiguousSlotInterval -- SNH 
                        SSApplyError err -> sAAApplyError err) sr)
            DAARError
        contFunApply t nwa nef np sr (DARNormal nc ni) =
          (symCaseApplyResult
             (\x -> case x of
                      SSApplied nst -> applyAllAux (n - 1) bnds (numPays + np) (numInps + ni)
                                                   env nst nc t nwa nef f
                      SSApplyError err -> f (sAAApplyError err) DAARError {- SNH -}) sr)

applyAll :: SymVal a => Bounds
         -> SEnvironment -> SState -> Contract -> SList NInput
         -> (SApplyAllResult -> DetApplyAllResult -> SBV a) -> SBV a
applyAll bnds env state c l f =
  applyAllAux (numActions bnds) bnds 0 0 env state c l [] [] f

-- PROCESS

-- List of signatures needed by a transaction
type STransactionSignatures = FSSet Party
type NTransactionSignatures = NSet Party

data ProcessError = PEReduceError NReduceError
                  | PEApplyError NApplyError
                  | PEIntervalError NIntervalError
                  | PEUselessTransaction
  deriving (Eq,Show)

mkSymbolicDatatype ''ProcessError

type ProcessWarning = ReduceWarning
type NProcessWarning = NReduceWarning
type SProcessWarning = SReduceWarning
type SSProcessWarning = SSReduceWarning

type ProcessEffect = ReduceEffect
type NProcessEffect = NReduceEffect
type SProcessEffect = SReduceEffect
type SSProcessEffect = SSReduceEffect

--data Transaction = Transaction { interval :: SSlotInterval
--                               , inputs   :: [SInput] }
--  deriving (Eq,Show)

type STransaction = STuple SlotInterval [NInput]
type NTransaction = (SlotInterval, [NInput])

interval :: STransaction -> SSlotInterval
interval x = let (si, _) = ST.untuple x in si

inputs :: STransaction -> SList NInput
inputs x = let (_, inps) = ST.untuple x in inps

-- Extract necessary signatures from transaction inputs

sFoldl :: SymVal a => SymVal b => Integer
       -> (SBV b -> SBV a -> SBV b) -> SBV b -> SList a -> SBV b
sFoldl inte f acc list
  | inte >= 0 = ite (SL.null list)
                   acc
                   (sFoldl (inte - 1) f (f acc (SL.head list)) (SL.tail list))
  | otherwise = acc 

getSignatures :: Bounds -> Integer -> SList NInput -> STransactionSignatures
getSignatures bnds numInps =
  sFoldl numInps (\x y -> symCaseInput (addSig x) y) FSSet.empty 
  where
    addSig acc (SSIDeposit _ p _) = FSSet.insert (numParties bnds) p acc
    addSig acc (SSIChoice t _) = let (_, p) = ST.untuple t in
                                 FSSet.insert (numParties bnds) p acc
    addSig acc SSINotify = acc

addIfPay :: Bounds -> SSReduceEffect -> STransactionOutcomes -> STransactionOutcomes 
addIfPay bnds (SSReduceNormalPay p m) to = addOutcome bnds p (-m) to
addIfPay _ _ to = to

addIfDep :: Bounds -> SSInput -> STransactionOutcomes -> STransactionOutcomes 
addIfDep bnds (SSIDeposit _ p m) to = addOutcome bnds p m to
addIfDep _ _ to = to

-- Extract total outcomes from transaction inputs and outputs
getOutcomesAux :: Bounds -> Integer -> Integer -> SList NReduceEffect -> SList NInput
               -> STransactionOutcomes -> STransactionOutcomes
getOutcomesAux bnds numPays numInps eff inp to
  | numPays >= 0 = ite (SL.null eff)
                      (getOutcomesAux bnds 0 numInps [] inp to)
                      (getOutcomesAux bnds (numPays - 1) numInps
                                      (SL.tail eff) inp
                                      (symCaseReduceEffect
                                         (\oneEff -> addIfPay bnds oneEff to)
                                         (SL.head eff)))
  | numInps >= 0 = ite (SL.null inp)
                      to 
                      (getOutcomesAux bnds 0 (numInps - 1)
                                      [] (SL.tail inp)
                                      (symCaseInput
                                         (\oneInp -> addIfDep bnds oneInp to)
                                         (SL.head inp)))
                                      
  | otherwise = to -- SNH 

getOutcomes :: Bounds -> Integer -> Integer -> SList NReduceEffect -> SList NInput
            -> STransactionOutcomes
getOutcomes bnds numPays numInps eff inp =
  getOutcomesAux bnds numPays numInps eff inp emptyOutcome 

data ProcessResult = Processed [NProcessWarning]
                               [NProcessEffect]
                               NTransactionSignatures
                               NTransactionOutcomes
                               State
                   | ProcessError NProcessError
  deriving (Eq,Show)


mkSymbolicDatatype ''ProcessResult


data DetProcessResult = DPProcessed Contract
                      | DPError

extractAppliedAll :: SymVal a => SSApplyAllResult
   -> (SBV [NProcessWarning] -> SBV [NProcessEffect] -> SBV State -> SBV a)
   -> SBV a
extractAppliedAll (SSAppliedAll wa ef nsta) f = f wa ef nsta 
extractAppliedAll (SSAAApplyError _) f = f [] [] (emptySState 0) -- SNH
extractAppliedAll (SSAAReduceError _) f = f [] [] (emptySState 0) -- SNH

convertProcessError :: SymVal a => SSApplyAllResult
                    -> (SProcessResult -> DetProcessResult -> SBV a) -> SBV a
convertProcessError (SSAppliedAll _ _ _) f =
  f (sProcessError $ sPEReduceError $ sReduceAmbiguousSlotInterval) DPError -- SNH
convertProcessError (SSAAApplyError aperr) f =
  f (sProcessError $ sPEApplyError aperr) DPError
convertProcessError (SSAAReduceError reerr) f =
  f (sProcessError $ sPEReduceError reerr) DPError

-- Try to process a transaction
processApplyResult :: SymVal a => Bounds -> STransaction -> Contract
                   -> (SProcessResult -> DetProcessResult -> SBV a)
                   -> SApplyAllResult -> DetApplyAllResult 
                   -> SBV a
processApplyResult bnds tra c f saar (DAARNormal ncon numPays numInps) =
  symCaseApplyAllResult
    (\aar ->
     extractAppliedAll aar
       (\wa ef nsta ->
        let sigs = getSignatures bnds numInps inps in
        let outcomes = getOutcomes bnds numPays numInps ef inps in
        if c == ncon
        then f (sProcessError sPEUselessTransaction) DPError
        else f (sProcessed wa ef sigs outcomes nsta) (DPProcessed ncon)))
    saar
  where inps = inputs tra
processApplyResult bnds tra c f saar DAARError =
  symCaseApplyAllResult
    (\aar -> convertProcessError aar f)
    saar

processAux :: SymVal a => Bounds -> STransaction -> SState -> Contract
           -> (SProcessResult -> DetProcessResult -> SBV a)
           -> SSIntervalResult -> SBV a
processAux bnds tra sta c f (SSIntervalTrimmed env fixSta) =
  applyAll bnds env fixSta c (inputs tra)
           (\sym det -> processApplyResult bnds tra c f sym det)
processAux bnds tra sta c f (SSIntervalError intErr) =
  f (sProcessError $ sPEIntervalError intErr) DPError

process :: SymVal a => Bounds -> STransaction -> SState -> Contract
        -> (SProcessResult -> DetProcessResult -> SBV a) -> SBV a
process bnds tra sta c f =
  symCaseIntervalResult (\interv -> processAux bnds tra sta c f interv)
                        (fixInterval (interval tra) sta)

extractProcessResult :: SProcessResult -> ( SList NProcessWarning
                                          , SList NProcessEffect
                                          , STransactionSignatures
                                          , STransactionOutcomes
                                          , SState)
extractProcessResult spr =
  ST.untuple (symCaseProcessResult prCases spr)
  where prCases (SSProcessed wa ef ts to nst) = ST.tuple (wa, ef, ts, to, nst)
        prCases (SSProcessError _) = ST.tuple ([], [], [], [], emptySState 0) -- SNH 

warningsTraceWBAux :: Integer -> Bounds -> SState -> SList NTransaction -> Contract
                   -> (SList NProcessWarning)
warningsTraceWBAux inte bnds st transList con
  | inte >= 0 = process bnds (SL.head transList) st con cont
  | otherwise = [] -- SNH 
  where cont spr (DPProcessed ncon) = let (wa, _, _, _, nst) = extractProcessResult spr in
                                      ite (SL.null $ wa)
                                          (warningsTraceWBAux (inte - 1) bnds nst
                                                              (SL.tail transList) ncon)
                                          wa
        cont spr DPError = []


warningsTraceWB :: Bounds -> SSlotNumber -> SList NTransaction -> Contract
                -> (SList NProcessWarning)
warningsTraceWB bnds sn transList con =
  warningsTraceWBAux (numActions bnds) bnds (emptySState sn) transList con

-- Adaptor functions

data Mappings = Mappings { partyM :: Numbering MS.Party
                         , choiceM :: Numbering MS.ChoiceId
                         , accountM :: Numbering MS.AccountId
                         , valueM :: Numbering MS.ValueId }

emptyMappings :: Mappings
emptyMappings = Mappings { partyM = emptyNumbering
                         , choiceM = emptyNumbering
                         , accountM = emptyNumbering
                         , valueM = emptyNumbering }

type MaxActions = Integer

convertTimeout :: MS.Timeout -> Timeout
convertTimeout (MS.Slot num) = num

convertParty :: MS.Party -> Mappings -> (Party, Mappings)
convertParty party maps@(Mappings { partyM = partyNumberings }) = (newParty, newMaps)
  where (newParty, newPartyNumberings) = getNumbering party partyNumberings
        newMaps = maps { partyM = newPartyNumberings }

convertAccId :: MS.AccountId -> Mappings -> (AccountId, Mappings)
convertAccId accId@(MS.AccountId _ party) maps =
    (AccountId newAccNum newParty, mapsWithParty)
  where accountNumberings = accountM maps
        (newAccNum, newAccountNumberings) = getNumbering accId accountNumberings
        mapsWithAccId = maps { accountM = newAccountNumberings }
        (newParty, mapsWithParty) = convertParty party mapsWithAccId

convertValId :: MS.ValueId -> Mappings -> (ValueId, Mappings)
convertValId valId maps@(Mappings { valueM = valueNumberings }) =
    (ValueId newValId, mapsWithValId)
  where valueNumberings = valueM maps
        (newValId, newValueNumberings) = getNumbering valId valueNumberings
        mapsWithValId = maps { valueM = newValueNumberings }

convertChoId :: MS.ChoiceId -> Mappings -> (ChoiceId, Mappings)
convertChoId choId@(MS.ChoiceId _ party) maps =
    (ChoiceId newChoNum newParty, mapsWithParty)
  where choiceNumberings = choiceM maps
        (newChoNum, newChoountNumberings) = getNumbering choId choiceNumberings
        mapsWithChoId = maps { choiceM = newChoountNumberings }
        (newParty, mapsWithParty) = convertParty party mapsWithChoId

convertPayee :: MS.Payee -> Mappings -> (Payee, Mappings)
convertPayee (MS.Account accId) maps = (Account (nestAccountId newAccId), mapsWithAccId)
  where (newAccId, mapsWithAccId) = convertAccId accId maps

convertBound :: MS.Bound -> Bound
convertBound (MS.Interval {MS.ivFrom = from, MS.ivTo = to}) = (from, to)

convertValue :: MS.Value -> Mappings -> (Value, Mappings)
convertValue (MS.AvailableMoney accId) maps =
    (AvailableMoney newAccId, mapsWithAccId)
  where (newAccId, mapsWithAccId) = convertAccId accId maps
convertValue (MS.Constant inte) maps =
    (Constant inte, maps)
convertValue (MS.NegValue val) maps =
    (NegValue newVal, mapsWithVal)
  where (newVal, mapsWithVal) = convertValue val maps
convertValue (MS.AddValue val1 val2) maps =
    (AddValue newVal1 newVal2, mapsWithVal2)
  where (newVal1, mapsWithVal1) = convertValue val1 maps
        (newVal2, mapsWithVal2) = convertValue val2 mapsWithVal1
convertValue (MS.SubValue val1 val2) maps =
    (SubValue newVal1 newVal2, mapsWithVal2)
  where (newVal1, mapsWithVal1) = convertValue val1 maps
        (newVal2, mapsWithVal2) = convertValue val2 mapsWithVal1
convertValue (MS.ChoiceValue choId val) maps =
    (ChoiceValue newChoId newVal, mapsWithVal)
  where (newChoId, mapsWithChoId) = convertChoId choId maps
        (newVal, mapsWithVal) = convertValue val mapsWithChoId
convertValue (MS.SlotIntervalStart) maps =
    (SlotIntervalStart, maps)
convertValue (MS.SlotIntervalEnd) maps =
    (SlotIntervalEnd, maps)
convertValue (MS.UseValue valId) maps =
    (UseValue newValId, mapsWithValId)
  where (newValId, mapsWithValId) = convertValId valId maps

convertObservation :: MS.Observation -> Mappings -> (Observation, Mappings)
convertObservation (MS.AndObs obs1 obs2) maps =
    (AndObs newObs1 newObs2, mapsWithObs2)
  where (newObs1, mapsWithObs1) = convertObservation obs1 maps
        (newObs2, mapsWithObs2) = convertObservation obs2 mapsWithObs1
convertObservation (MS.OrObs obs1 obs2) maps =
    (OrObs newObs1 newObs2, mapsWithObs2)
  where (newObs1, mapsWithObs1) = convertObservation obs1 maps
        (newObs2, mapsWithObs2) = convertObservation obs2 mapsWithObs1
convertObservation (MS.NotObs obs) maps =
    (NotObs newObs, mapsWithObs)
  where (newObs, mapsWithObs) = convertObservation obs maps
convertObservation (MS.ChoseSomething choId) maps =
    (ChoseSomething newChoId, mapsWithChoId)
  where (newChoId, mapsWithChoId) = convertChoId choId maps
convertObservation (MS.ValueGE val1 val2) maps =
    (ValueGE newVal1 newVal2, mapsWithVal2)
  where (newVal1, mapsWithVal1) = convertValue val1 maps
        (newVal2, mapsWithVal2) = convertValue val2 mapsWithVal1
convertObservation (MS.ValueGT val1 val2) maps =
    (ValueGT newVal1 newVal2, mapsWithVal2)
  where (newVal1, mapsWithVal1) = convertValue val1 maps
        (newVal2, mapsWithVal2) = convertValue val2 mapsWithVal1
convertObservation (MS.ValueLT val1 val2) maps =
    (ValueLT newVal1 newVal2, mapsWithVal2)
  where (newVal1, mapsWithVal1) = convertValue val1 maps
        (newVal2, mapsWithVal2) = convertValue val2 mapsWithVal1
convertObservation (MS.ValueLE val1 val2) maps =
    (ValueLE newVal1 newVal2, mapsWithVal2)
  where (newVal1, mapsWithVal1) = convertValue val1 maps
        (newVal2, mapsWithVal2) = convertValue val2 mapsWithVal1
convertObservation (MS.ValueEQ val1 val2) maps =
    (ValueEQ newVal1 newVal2, mapsWithVal2)
  where (newVal1, mapsWithVal1) = convertValue val1 maps
        (newVal2, mapsWithVal2) = convertValue val2 mapsWithVal1
convertObservation (MS.TrueObs) maps = (TrueObs, maps)
convertObservation (MS.FalseObs) maps = (FalseObs, maps)

convertAction :: MS.Action -> Mappings -> (Action, Mappings)
convertAction (MS.Deposit accId party value) maps =
    (Deposit newAccId newParty newValue, mapsWithValue)
  where (newAccId, mapsWithAccId) = convertAccId accId mapsWithAccId
        (newParty, mapsWithParty) = convertParty party mapsWithParty
        (newValue, mapsWithValue) = convertValue value mapsWithValue
convertAction (MS.Choice choId bounds) maps =
    (Choice newChoId newBounds, mapsWithChoId)
  where (newChoId, mapsWithChoId) = convertChoId choId maps
        newBounds = map convertBound bounds
convertAction (MS.Notify observation) maps =
    (Notify newObservation, mapsWithObservation)
  where (newObservation, mapsWithObservation) = convertObservation observation maps

convertCaseList :: [MS.Case] -> Mappings -> ([Case], MaxActions, Mappings)
convertCaseList [] maps = ([], 0, maps)
convertCaseList (MS.Case action cont : rest) maps =
    ((Case newAction newCont : newRest), max actionsWithCont actionsWithRest, mapsWithRest)
  where (newAction, mapsWithAction) = convertAction action maps
        (newCont, actionsWithCont, mapsWithCont) = convertContract cont mapsWithAction
        (newRest, actionsWithRest, mapsWithRest) = convertCaseList rest mapsWithCont

convertContract :: MS.Contract -> Mappings -> (Contract, MaxActions, Mappings)
convertContract MS.Refund maps = (Refund, 0, maps)
convertContract (MS.Pay accId payee value cont) maps =
    (Pay newAccId newPayee newValue newCont, actionsWithCont, mapsWithContract)
  where (newAccId, mapsWithAccId) = convertAccId accId maps
        (newPayee, mapsWithPayee) = convertPayee payee mapsWithAccId
        (newValue, mapsWithValue) = convertValue value mapsWithPayee
        (newCont, actionsWithCont, mapsWithContract) = convertContract cont mapsWithValue
convertContract (MS.If obs cont1 cont2) maps =
    (If newObs newCont1 newCont2, actionsWithCont2, mapsWithCont2)
  where (newObs, mapsWithObs) = convertObservation obs maps
        (newCont1, actionsWithCont1, mapsWithCont1) = convertContract cont1 mapsWithObs
        (newCont2, actionsWithCont2, mapsWithCont2) = convertContract cont2 mapsWithCont1
convertContract (MS.When caseList timeout cont) maps =
    ( When newCaseList newTimeout newCont
    , max actionsWithCaseList actionsWithCont
    , mapsWithCont)
  where (newCaseList, actionsWithCaseList, mapsWithCaseList) = convertCaseList caseList maps
        newTimeout = convertTimeout timeout
        (newCont, actionsWithCont, mapsWithCont) = convertContract cont mapsWithCaseList
convertContract (MS.Let valId value cont) maps =
    (Let newValId newValue newCont, actionsWithCont, mapsWithContract)
  where (newValId, mapsWithValId) = convertValId valId maps
        (newValue, mapsWithValue) = convertValue value mapsWithValId
        (newCont, actionsWithCont, mapsWithContract) = convertContract cont mapsWithValue 

convertContractBase :: MS.Contract -> (Contract, MaxActions, Mappings)
convertContractBase c = convertContract c emptyMappings

