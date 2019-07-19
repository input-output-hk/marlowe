{-# LANGUAGE NamedFieldPuns #-}
module Semantics4 where

import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Set        (Set)
import qualified Data.Set        as S

type SlotNumber = Integer
type SlotInterval = (SlotNumber, SlotNumber)
type PubKey = Integer
type Party = PubKey
type NumChoice = Integer
type NumAccount = Integer
type Timeout = SlotNumber
type Money = Integer
type ChosenNum = Integer
type ValueId = Integer

data AccountId = AccountId NumAccount Party
  deriving (Eq,Ord,Show,Read)

accountOwner :: AccountId -> Party
accountOwner (AccountId _ party) = party

data ChoiceId = ChoiceId NumChoice Party
  deriving (Eq,Ord,Show,Read)
newtype OracleId = OracleId PubKey
  deriving (Eq,Ord,Show,Read)

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

type Bound = (SlotNumber, SlotNumber)

inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = any (\(l, u) -> num >= l && num <= u)

data Action = Deposit AccountId Party Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving (Eq,Ord,Show,Read)

data Case = Case Action Contract
  deriving (Eq,Ord,Show,Read)

data Payee = Account AccountId
           | Party Party
  deriving (Eq,Ord,Show,Read)

data Contract = RefundAll
              | Pay AccountId Payee Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract
              | Let ValueId Value Contract
  deriving (Eq,Ord,Show,Read)

data State = State { account :: Map AccountId Money
                   , choice  :: Map ChoiceId ChosenNum
                   , boundValues :: Map ValueId Integer
                   , minSlot :: SlotNumber }
  deriving (Eq,Ord,Show,Read)

data Environment = Environment { slotInterval :: SlotInterval }
  deriving (Eq,Ord,Show,Read)

data Input = IDeposit AccountId Party Money
           | IChoice ChoiceId ChosenNum
           | INotify
  deriving (Eq,Ord,Show,Read)

-- TRANSACTION OUTCOMES

type TransactionOutcomes = M.Map Party Money

emptyOutcome :: TransactionOutcomes
emptyOutcome = M.empty

isEmptyOutcome :: TransactionOutcomes -> Bool
isEmptyOutcome trOut = all (== 0) trOut

-- Adds a value to the map of outcomes
addOutcome :: Party -> Money -> TransactionOutcomes -> TransactionOutcomes
addOutcome party diffValue trOut = M.insert party newValue trOut
  where
    newValue = case M.lookup party trOut of
        Just value -> value + diffValue
        Nothing    -> diffValue

-- Add two transaction outcomes together
combineOutcomes :: TransactionOutcomes -> TransactionOutcomes -> TransactionOutcomes
combineOutcomes = M.unionWith (+)

-- INTERVALS

-- Processing of slot interval
data IntervalError = InvalidInterval SlotInterval
                   | IntervalInPastError SlotNumber SlotInterval
  deriving (Eq,Ord,Show,Read)

data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError IntervalError
  deriving (Eq,Ord,Show,Read)

fixInterval :: SlotInterval -> State -> IntervalResult
fixInterval i@(l, h) st@State{minSlot} | h < l = IntervalError $ InvalidInterval i
                                       | h < minSlot = IntervalError $ IntervalInPastError minSlot i
                                       | otherwise = IntervalTrimmed env nst
  where
    nl = max l minSlot -- nl is both new "l" and new "minSlot" (the lower bound for slotNum)
    tInt = (nl, h) -- We know h is greater or equal than nl (prove)
    env = Environment tInt
    nst = st { minSlot = nl }

-- EVALUATION

-- Evaluate a value
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value = case value of
    AvailableMoney accId     -> M.findWithDefault 0 accId $ account state
    Constant integer         -> integer
    NegValue val             -> go val
    AddValue lhs rhs         -> go lhs + go rhs
    SubValue lhs rhs         -> go lhs + go rhs
    ChoiceValue choId defVal -> M.findWithDefault (go defVal) choId $ choice state
    SlotIntervalStart        -> fst $ slotInterval env
    SlotIntervalEnd          -> snd $ slotInterval env
    UseValue valId           -> M.findWithDefault 0 valId $ boundValues state
  where go = evalValue env state

-- Evaluate an observation
evalObservation :: Environment -> State -> Observation -> Bool
evalObservation env state obs = case obs of
    AndObs lhs rhs       -> goObs lhs && goObs rhs
    OrObs lhs rhs        -> goObs lhs || goObs rhs
    NotObs subObs        -> not $ goObs subObs
    ChoseSomething choId -> choId `M.member` choice state
    ValueGE lhs rhs      -> goVal lhs >= goVal rhs
    ValueGT lhs rhs      -> goVal lhs > goVal rhs
    ValueLT lhs rhs      -> goVal lhs < goVal rhs
    ValueLE lhs rhs      -> goVal lhs <= goVal rhs
    ValueEQ lhs rhs      -> goVal lhs == goVal rhs
    TrueObs              -> True
    FalseObs             -> False
  where
    goObs = evalObservation env state
    goVal = evalValue env state

-- Pick the first account with money in it
refundOne :: Map AccountId Money -> Maybe ((Party, Money), Map AccountId Money)
refundOne accounts = do
    ((accId, mon), rest) <- M.minViewWithKey accounts
    if mon > 0 then return ((accountOwner accId, mon), rest) else refundOne rest

-- Obtains the amount of money available an account
moneyInAccount :: Map AccountId Money -> AccountId -> Money
moneyInAccount accs accId = M.findWithDefault 0 accId accs

-- Sets the amount of money available in an account
updateMoneyInAccount :: Map AccountId Money -> AccountId -> Money -> Map AccountId Money
updateMoneyInAccount accs accId mon | mon <= 0 = M.delete accId accs
                                    | otherwise = M.insert accId mon accs

-- Withdraw up to the given amount of money from an account
-- Return the amount of money withdrawn
withdrawMoneyFromAccount
    :: Map AccountId Money -> AccountId -> Money -> (Money, Map AccountId Money)
withdrawMoneyFromAccount accs accId mon = (withdrawnMoney, newAcc)
  where
    avMoney = moneyInAccount accs accId
    withdrawnMoney = min avMoney mon
    newAvMoney = avMoney - withdrawnMoney
    newAcc = updateMoneyInAccount accs accId newAvMoney

-- Add the given amount of money to an accoun (only if it is positive)
-- Return the updated Map
addMoneyToAccount :: Map AccountId Money -> AccountId -> Money -> Map AccountId Money
addMoneyToAccount accs accId mon | mon <= 0 = accs
                                 | otherwise = updateMoneyInAccount accs accId newAvMoney
  where
    avMoney = moneyInAccount accs accId
    newAvMoney = avMoney + mon

-- Gives the given amount of money to the given payee
-- Return the appropriate effect and updated Map
giveMoney :: Map AccountId Money -> Payee -> Money -> (ReduceEffect, Map AccountId Money)
giveMoney accs (Party party) mon = (ReduceNormalPay party mon, accs)
giveMoney accs (Account accId) mon = (ReduceNoEffect, newAccs)
    where newAccs = addMoneyToAccount accs accId mon

-- REDUCE

data ReduceWarning = ReduceNoWarning
                   | ReduceNonPositivePay AccountId Payee Money
                   | ReducePartialPay AccountId Payee Money Money
                                    -- ^ src    ^ dest ^ paid ^ expected
                   | ReduceShadowing ValueId Integer Integer
                                     -- oldVal ^  newVal ^
  deriving (Eq,Ord,Show,Read)

data ReduceEffect = ReduceNoEffect
                  | ReduceNormalPay Party Money
  deriving (Eq,Ord,Show,Read)

data ReduceError = ReduceAmbiguousSlotInterval
  deriving (Eq,Ord,Show,Read)

data ReduceResult = Reduced ReduceWarning ReduceEffect State Contract
                  | NotReduced
                  | ReduceError ReduceError
  deriving (Eq,Ord,Show,Read)

-- Carry a step of the contract with no inputs
reduce :: Environment -> State -> Contract -> ReduceResult
reduce _ state c@RefundAll = case refundOne $ account state of
    (Just ((party, money), newAccount)) ->
        let newState = state { account = newAccount }
        in  Reduced ReduceNoWarning (ReduceNormalPay party money) newState c
    Nothing -> NotReduced
reduce env state (Pay accId payee val nc) = if mon <= 0
    then Reduced (ReduceNonPositivePay accId payee mon) ReduceNoEffect state nc
    else Reduced noMonWarn payEffect (state { account = finalAccs }) nc
  where
    mon = evalValue env state val
    (paidMon, newAccs) = withdrawMoneyFromAccount (account state) accId mon
    noMonWarn = if paidMon < mon then ReducePartialPay accId payee paidMon mon else ReduceNoWarning
    (payEffect, finalAccs) = giveMoney newAccs payee paidMon
reduce env state (If obs cont1 cont2) = Reduced ReduceNoWarning ReduceNoEffect state nc
  where nc = if evalObservation env state obs then cont1 else cont2
reduce env state (When _ timeout c)
    | endSlot < timeout = NotReduced
    | startSlot >= timeout = Reduced ReduceNoWarning ReduceNoEffect state c
    | otherwise = ReduceError ReduceAmbiguousSlotInterval
  where
    startSlot = fst $ slotInterval env
    endSlot = snd $ slotInterval env
reduce env state (Let valId val cont) =
    Reduced warn ReduceNoEffect ns cont
  where
    sv = boundValues $ state
    evVal = evalValue env state val
    nsv = M.insert valId evVal sv
    ns = state { boundValues = nsv }
    warn = case M.lookup valId sv of
             Just oldVal -> ReduceShadowing valId oldVal evVal
             Nothing -> ReduceNoWarning

-- REDUCE ALL

data ReduceAllResult = ReducedAll [ReduceWarning] [ReduceEffect] State Contract
                     | ReduceAllError ReduceError
  deriving (Eq,Ord,Show,Read)

-- Reduce until it cannot be reduced more
reduceAllAux
    :: Environment -> State -> Contract -> [ReduceWarning] -> [ReduceEffect] -> ReduceAllResult
reduceAllAux env sta c wa ef = case reduce env sta c of
    Reduced twa tef nsta nc ->
        let nwa = if twa == ReduceNoWarning then wa else twa : wa
        in  let nef = if tef == ReduceNoEffect then ef else tef : ef
            in  reduceAllAux env nsta nc nwa nef
    ReduceError err -> ReduceAllError err
    NotReduced -> ReducedAll (reverse wa) (reverse ef) sta c

reduceAll :: Environment -> State -> Contract -> ReduceAllResult
reduceAll env sta c = reduceAllAux env sta c [] []

-- APPLY

data ApplyError = ApplyNoMatch
  deriving (Eq,Ord,Show,Read)

data ApplyResult = Applied State Contract
                 | ApplyError ApplyError
  deriving (Eq,Ord,Show,Read)

-- Apply a single Input to the contract (assumes the contract is reduced)
applyCases :: Environment -> State -> Input -> [Case] -> ApplyResult
applyCases env state (IDeposit accId1 party1 mon1) (Case (Deposit accId2 party2 val2) nc : _)
    | accId1 == accId2 && party1 == party2 && mon1 == mon2 = Applied newState nc
  where
    mon2 = evalValue env state val2
    accs = account state
    newAccs = addMoneyToAccount accs accId1 mon1
    newState = state { account = newAccs }
applyCases _ state (IChoice choId1 cho1) (Case (Choice choId2 bounds2) nc : _)
    | choId1 == choId2 && inBounds cho1 bounds2 = Applied newState nc
    where newState = state { choice = M.insert choId1 cho1 $ choice state }
applyCases env state INotify (Case (Notify obs) nc : _) | evalObservation env state obs =
    Applied state nc
applyCases env state act (_ : t) = applyCases env state act t
applyCases _ _ _ [] = ApplyError ApplyNoMatch

apply :: Environment -> State -> Input -> Contract -> ApplyResult
apply env state act (When cases _ _) = applyCases env state act cases
apply _ _ _ _                        = ApplyError ApplyNoMatch

-- APPLY ALL

data ApplyAllResult = AppliedAll [ReduceWarning] [ReduceEffect] State Contract
                    | AAApplyError ApplyError
                    | AAReduceError ReduceError
  deriving (Eq,Ord,Show,Read)

-- Apply a list of Inputs to the contract
applyAllAux
    :: Environment
    -> State
    -> Contract
    -> [Input]
    -> [ReduceWarning]
    -> [ReduceEffect]
    -> ApplyAllResult
applyAllAux env state c l wa ef = case reduceAll env state c of
    ReduceAllError raerr -> AAReduceError raerr
    ReducedAll twa tef tstate tc -> case l of
        [] -> AppliedAll (wa ++ twa) (ef ++ tef) tstate tc
        (h : t) -> case apply env tstate h tc of
            Applied nst nc   -> applyAllAux env nst nc t (wa ++ twa) (ef ++ tef)
            ApplyError aeerr -> AAApplyError aeerr

applyAll :: Environment -> State -> Contract -> [Input] -> ApplyAllResult
applyAll env state c l = applyAllAux env state c l [] []

-- PROCESS

-- List of signatures needed by a transaction
type TransactionSignatures = Set Party

data ProcessError = PEReduceError ReduceError
                  | PEApplyError ApplyError
                  | PEIntervalError IntervalError
                  | PEUselessTransaction
  deriving (Eq,Ord,Show,Read)

type ProcessWarning = ReduceWarning
type ProcessEffect = ReduceEffect

data ProcessResult = Processed [ProcessWarning]
                               [ProcessEffect]
                               TransactionSignatures
                               TransactionOutcomes
                               State
                               Contract
                   | ProcessError ProcessError
  deriving (Eq,Ord,Show,Read)

data Transaction = Transaction { interval :: SlotInterval
                               , inputs   :: [Input] }
  deriving (Eq,Ord,Show,Read)

-- Extract necessary signatures from transaction inputs
getSignatures :: [Input] -> TransactionSignatures
getSignatures = foldl' addSig S.empty
  where
    addSig acc (IDeposit _ p _)           = S.insert p acc
    addSig acc (IChoice (ChoiceId _ p) _) = S.insert p acc
    addSig acc INotify                    = acc

-- Extract total outcomes from transaction inputs and outputs
getOutcomes :: [ReduceEffect] -> [Input] -> TransactionOutcomes
getOutcomes eff inp = foldl' (\acc (p, m) -> addOutcome p m acc) emptyOutcome (incomes ++ outcomes)
  where
    incomes = [ (p, m) | ReduceNormalPay p m <- eff ]
    outcomes = [ (p, m) | IDeposit _ p m <- inp ]

-- Try to process a transaction
process :: Transaction -> State -> Contract -> ProcessResult
process tra sta c = case fixInterval (interval tra) sta of
    IntervalTrimmed env fixSta -> case applyAll env fixSta c inps of
        AppliedAll wa ef nsta ncon ->
            let sigs = getSignatures inps
            in  let outcomes = getOutcomes ef inps
                in  if c == ncon
                    then ProcessError PEUselessTransaction
                    else Processed wa ef sigs outcomes nsta ncon
        AAApplyError aperr -> ProcessError $ PEApplyError aperr
        AAReduceError reerr -> ProcessError $ PEReduceError reerr
    IntervalError intErr -> ProcessError $ PEIntervalError intErr
  where inps = inputs tra

-- Calculates an upper bound for the maximum lifespan of a contract
contractLifespan :: Contract -> Integer
contractLifespan contract = case contract of
    RefundAll -> 0
    Pay _ _ _ cont -> contractLifespan cont
    -- TODO simplify observation and check for always true/false cases
    If _ contract1 contract2 ->
        max (contractLifespan contract1) (contractLifespan contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespan cont) cases
        in maximum (timeout : contractLifespan subContract : contractsLifespans)
    Let _ _ cont -> contractLifespan cont

