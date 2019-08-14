{-# LANGUAGE NamedFieldPuns #-}
module Semantics4 where

import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set

type SlotNumber = Integer
type SlotInterval = (SlotNumber, SlotNumber)
type PubKey = Integer
type Party = PubKey
type NumChoice = Integer
type NumAccount = Integer
type Timeout = SlotNumber
type Money = Integer
type ChosenNum = Integer

data AccountId = AccountId NumAccount Party
  deriving (Eq,Ord,Show,Read)

accountOwner :: AccountId -> Party
accountOwner (AccountId _ party) = party

data ChoiceId = ChoiceId NumChoice Party
  deriving (Eq,Ord,Show,Read)
newtype OracleId = OracleId PubKey
  deriving (Eq,Ord,Show,Read)
newtype ValueId = ValueId Integer
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

data State = State { accounts :: Map AccountId Money
                   , choices  :: Map ChoiceId ChosenNum
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

type TransactionOutcomes = Map Party Money


emptyOutcome :: TransactionOutcomes
emptyOutcome = Map.empty


isEmptyOutcome :: TransactionOutcomes -> Bool
isEmptyOutcome trOut = all (== 0) trOut


-- Adds a value to the map of outcomes
addOutcome :: Party -> Money -> TransactionOutcomes -> TransactionOutcomes
addOutcome party diffValue trOut = Map.insert party newValue trOut
  where
    newValue = case Map.lookup party trOut of
        Just value -> value + diffValue
        Nothing    -> diffValue


-- Add two transaction outcomes together
combineOutcomes :: TransactionOutcomes -> TransactionOutcomes -> TransactionOutcomes
combineOutcomes = Map.unionWith (+)

-- INTERVALS

-- Processing of slot interval
data IntervalError = InvalidInterval SlotInterval
                   | IntervalInPastError SlotNumber SlotInterval
  deriving (Eq,Ord,Show,Read)

data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError IntervalError
  deriving (Eq,Ord,Show,Read)


fixInterval :: SlotInterval -> State -> IntervalResult
fixInterval interval@(low, high) state@State{minSlot}
    | high < low = IntervalError $ InvalidInterval interval
    | high < minSlot = IntervalError $ IntervalInPastError minSlot interval
    | otherwise = IntervalTrimmed env nst
  where
    -- newLow is both new "low" and new "minSlot" (the lower bound for slotNum)
    newLow = max low minSlot
    tInt = (newLow, high) -- We know high is greater or equal than newLow (prove)
    env = Environment tInt
    nst = state { minSlot = newLow }

-- EVALUATION

-- Evaluate a value
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value = case value of
    AvailableMoney accId     -> Map.findWithDefault 0 accId $ accounts state
    Constant integer         -> integer
    NegValue val             -> go val
    AddValue lhs rhs         -> go lhs + go rhs
    SubValue lhs rhs         -> go lhs + go rhs
    ChoiceValue choiceId defVal -> Map.findWithDefault (go defVal) choiceId $ choices state
    SlotIntervalStart        -> fst $ slotInterval env
    SlotIntervalEnd          -> snd $ slotInterval env
    UseValue valId           -> Map.findWithDefault 0 valId $ boundValues state
  where go = evalValue env state


-- Evaluate an observation
evalObservation :: Environment -> State -> Observation -> Bool
evalObservation env state obs = case obs of
    AndObs lhs rhs       -> goObs lhs && goObs rhs
    OrObs lhs rhs        -> goObs lhs || goObs rhs
    NotObs subObs        -> not $ goObs subObs
    ChoseSomething choiceId -> choiceId `Map.member` choices state
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


-- | Pick the first account with money in it
refundOne :: Map AccountId Money -> Maybe ((Party, Money), Map AccountId Money)
refundOne accounts = do
    ((accId, money), rest) <- Map.minViewWithKey accounts
    if money > 0 then return ((accountOwner accId, money), rest) else refundOne rest


-- | Obtains the amount of money available an account
moneyInAccount :: AccountId -> Map AccountId Money -> Money
moneyInAccount = Map.findWithDefault 0


-- | Sets the amount of money available in an account
updateMoneyInAccount :: AccountId -> Money -> Map AccountId Money -> Map AccountId Money
updateMoneyInAccount accId money =
    if money <= 0 then Map.delete accId else Map.insert accId money


{-| Withdraw up to the given amount of money from an account
    Return the amount of money withdrawn
-}
withdrawMoneyFromAccount
  :: AccountId -> Money -> Map AccountId Money -> (Money, Map AccountId Money)
withdrawMoneyFromAccount accId money accounts = (withdrawnMoney, newAcc)
  where
    avMoney        = moneyInAccount accId accounts
    withdrawnMoney = min avMoney money
    newAvMoney     = avMoney - withdrawnMoney
    newAcc         = updateMoneyInAccount accId newAvMoney accounts


{-| Add the given amount of money to an accoun (only if it is positive).
    Return the updated Map
-}
addMoneyToAccount :: AccountId -> Money -> Map AccountId Money -> Map AccountId Money
addMoneyToAccount accId money accounts =
    if money <= 0 then accounts else updateMoneyInAccount accId newAvMoney accounts
  where
    avMoney = moneyInAccount accId accounts
    newAvMoney = avMoney + money


{-| Gives the given amount of money to the given payee.
    Returns the appropriate effect and updated accounts
-}
giveMoney :: Payee -> Money -> Map AccountId Money -> (ReduceEffect, Map AccountId Money)
giveMoney (Party   party) money accounts = (ReduceNormalPay party money, accounts)
giveMoney (Account accId) money accounts = (ReduceNoEffect, newAccs)
  where newAccs = addMoneyToAccount accId money accounts

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


-- | Carry a step of the contract with no inputs
reduce :: Environment -> State -> Contract -> ReduceResult
reduce env state contract = case contract of
    Refund -> case refundOne $ accounts state of
        Just ((party, money), newAccounts) ->
            let newState = state { accounts = newAccounts }
            in  Reduced ReduceNoWarning (ReduceNormalPay party money) newState Refund
        Nothing -> NotReduced
    Pay accId payee val cont -> if amountToPay <= 0
        then Reduced (ReduceNonPositivePay accId payee amountToPay) ReduceNoEffect state cont
        else let
                (paidMoney, newAccs) = withdrawMoneyFromAccount accId amountToPay $ accounts state
                paidAmount = paidMoney
                warning = if paidAmount < amountToPay
                          then ReducePartialPay accId payee paidAmount amountToPay
                          else ReduceNoWarning
                (payEffect, finalAccs) = giveMoney payee paidMoney newAccs
            in Reduced warning payEffect (state { accounts = finalAccs }) cont
      where amountToPay = evalValue env state val
    If obs cont1 cont2 -> Reduced ReduceNoWarning ReduceNoEffect state cont
      where cont = if evalObservation env state obs then cont1 else cont2
    When _ timeout cont
        -- if timeout in future – do not reduce
        | endSlot < timeout -> NotReduced
        -- if timeout in the past – reduce to timeout continuation
        | timeout <= startSlot -> Reduced ReduceNoWarning ReduceNoEffect state cont
        -- if timeout in the slot range – issue an ambiguity error
        | otherwise -> ReduceError ReduceAmbiguousSlotInterval
      where
        startSlot = fst $ slotInterval env
        endSlot   = snd $ slotInterval env
    Let valId val cont -> Reduced warn ReduceNoEffect newState cont
      where
        evVal = evalValue env state val
        boundVals = boundValues state
        newState = state { boundValues = Map.insert valId evVal boundVals }
        warn = case Map.lookup valId boundVals of
              Just oldVal -> ReduceShadowing valId oldVal evVal
              Nothing -> ReduceNoWarning


-- REDUCE ALL

data ReduceAllResult = ReducedAll [ReduceWarning] [ReduceEffect] State Contract
                     | ReduceAllError ReduceError
  deriving (Eq,Ord,Show,Read)

-- Reduce until it cannot be reduced more
reduceAllAux
  :: Environment -> State -> Contract -> [ReduceWarning] -> [ReduceEffect] -> ReduceAllResult
reduceAllAux env state contract warnings effects = case reduce env state contract of
    Reduced warning effect newState cont -> let
        newWarnings = if warning == ReduceNoWarning then warnings else warning : warnings
        newEffects  = if effect  == ReduceNoEffect  then effects  else effect : effects
        in  reduceAllAux env newState cont newWarnings newEffects
    ReduceError err -> ReduceAllError err
    NotReduced -> ReducedAll (reverse warnings) (reverse effects) state contract


reduceAll :: Environment -> State -> Contract -> ReduceAllResult
reduceAll env state contract = reduceAllAux env state contract [] []

-- APPLY

data ApplyError = ApplyNoMatch
  deriving (Eq,Ord,Show,Read)

data ApplyResult = Applied State Contract
                 | ApplyError ApplyError
  deriving (Eq,Ord,Show,Read)


-- Apply a single Input to the contract (assumes the contract is reduced)
applyCases :: Environment -> State -> Input -> [Case] -> ApplyResult
applyCases env state input cases = case (input, cases) of
    (IDeposit accId1 party1 money, Case (Deposit accId2 party2 val) cont : _)
      | accId1 == accId2 && party1 == party2 && money == amount -> Applied newState cont
      where
        amount = evalValue env state val
        newState = state { accounts = addMoneyToAccount accId1 money $ accounts state }
    (IChoice choId1 choice, Case (Choice choId2 bounds) cont : _)
      | choId1 == choId2 && inBounds choice bounds -> Applied newState cont
      where newState = state { choices = Map.insert choId1 choice $ choices state }
    (_, Case (Notify obs) cont : _) | evalObservation env state obs -> Applied state cont
    (_, _ : rest) -> applyCases env state input rest
    (_, []) -> ApplyError ApplyNoMatch


apply :: Environment -> State -> Input -> Contract -> ApplyResult
apply env state input (When cases _ _) = applyCases env state input cases
apply _ _ _ _                          = ApplyError ApplyNoMatch

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
applyAllAux env state contract inputs warnings effects = case reduceAll env state contract of
    ReduceAllError error -> AAReduceError error
    ReducedAll warns effs curState cont -> case inputs of
        [] -> AppliedAll (warnings ++ warns) (effects ++ effs) curState cont
        (input : rest) -> case apply env curState input cont of
            Applied newState cont ->
                applyAllAux env newState cont rest (warnings ++ warns) (effects ++ effs)
            ApplyError error -> AAApplyError error


applyAll :: Environment -> State -> Contract -> [Input] -> ApplyAllResult
applyAll env state contract inputs = applyAllAux env state contract inputs [] []

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

data Transaction = Transaction { txInterval :: SlotInterval
                               , txInputs   :: [Input] }
  deriving (Eq,Ord,Show,Read)


-- | Extract necessary signatures from transaction inputs
getSignatures :: [Input] -> TransactionSignatures
getSignatures = foldl' addSig Set.empty
  where
    addSig acc (IDeposit _ p _)           = Set.insert p acc
    addSig acc (IChoice (ChoiceId _ p) _) = Set.insert p acc
    addSig acc INotify                    = acc


-- | Extract total outcomes from transaction inputs and outputs
getOutcomes :: [ReduceEffect] -> [Input] -> TransactionOutcomes
getOutcomes effect input =
  foldl' (\acc (p, m) -> addOutcome p m acc) emptyOutcome (incomes ++ outcomes)
  where
    incomes = [ (p, m) | ReduceNormalPay p m <- effect ]
    outcomes = [ (p, m) | IDeposit _ p m <- input ]


-- | Try to process a transaction
processTransaction :: Transaction -> State -> Contract -> ProcessResult
processTransaction tx state contract = case fixInterval (txInterval tx) state of
    IntervalTrimmed env fixState -> case applyAll env fixState contract inputs of
        AppliedAll warnings effects newState cont ->
            let sigs = getSignatures inputs
            in  let outcomes = getOutcomes effects inputs
                in  if contract == cont
                    then ProcessError PEUselessTransaction
                    else Processed warnings effects sigs outcomes newState cont
        AAApplyError error -> ProcessError $ PEApplyError error
        AAReduceError error -> ProcessError $ PEReduceError error
    IntervalError error -> ProcessError $ PEIntervalError error
  where inputs = txInputs tx


-- Calculates an upper bound for the maximum lifespan of a contract
contractLifespan :: Contract -> Integer
contractLifespan contract = case contract of
    Refund -> 0
    Pay _ _ _ cont -> contractLifespan cont
    -- TODO simplify observation and check for always true/false cases
    If _ contract1 contract2 ->
        max (contractLifespan contract1) (contractLifespan contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespan cont) cases
        in maximum (timeout : contractLifespan subContract : contractsLifespans)
    Let _ _ cont -> contractLifespan cont
