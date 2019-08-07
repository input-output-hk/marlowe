{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}
module FSSemantics where

import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Set        (Set)
import qualified Data.Set        as S
import           Data.SBV
import qualified Data.SBV.Tuple as ST
import qualified Data.SBV.Either as SE
import qualified Data.SBV.Maybe as SM
import qualified FSMap as FSMap
import           FSMap(FSMap)
import           MkSymb(mkSymbolicDatatype)

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

--data AccountId = AccountId NumAccount Party
--  deriving (Eq,Ord,Show,Read)
data AccountId = AccountId NumAccount Party
  deriving (Eq,Ord,Show,Read)
type NAccountId = (NumAccount, Party)
type SAccountId = STuple NumAccount Party

sAccountId :: NumAccount -> Party -> SAccountId
sAccountId a p = ST.tuple (literal a, literal p)

accountOwner :: AccountId -> Party
accountOwner (AccountId _ party) = party

data ChoiceId = ChoiceId NumChoice Party
  deriving (Eq,Ord,Show,Read)
type NChoiceId = (NumChoice, Party)
type SChoiceId = STuple NumChoice Party

sChoiceId :: NumChoice -> Party -> SChoiceId
sChoiceId c p = ST.tuple (literal c, literal p)

newtype OracleId = OracleId PubKey
  deriving (Eq,Ord,Show,Read)

newtype ValueId = ValueId Integer
  deriving (Eq,Ord,Show,Read)
type NValueId = Integer
type SValueId = SInteger

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

inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = any (\(l, u) -> num >= l && num <= u)

data Action = Deposit AccountId Party Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving (Eq,Ord,Show,Read)

data Payee = Account AccountId
           | Party Party
  deriving (Eq,Ord,Show,Read)

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
type SState = STuple4 [(NAccountId, Money)]
                      [(NChoiceId, ChosenNum)]
                      [(NValueId, Integer)]
                      SlotNumber
type State = ( [(NAccountId, Money)]
             , [(NChoiceId, ChosenNum)]
             , [(NValueId, Integer)]
             , SlotNumber)

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
data SInput = IDeposit AccountId Party Money
            | IChoice ChoiceId ChosenNum
            | INotify
  deriving (Eq,Ord,Show,Read)

data Bounds = Bounds { numParties :: Integer
                     , numChoices :: Integer
                     , numAccounts :: Integer
                     , numLets :: Integer
                     }

-- TRANSACTION OUTCOMES

type STransactionOutcomes = FSMap Party Money

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

