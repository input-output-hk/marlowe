module Semantics4 where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

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
data OracleId = OracleId PubKey
  deriving (Eq,Ord,Show,Read)

data Value = AvailableMoney AccountId 
           | Constant Integer
           | NegValue Value
           | AddValue Value Value
           | SubValue Value Value
           | ChoiceValue ChoiceId Value
           | SlotIntervalStart
           | SlotIntervalEnd
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
  deriving (Eq,Ord,Show,Read)

data State = State { account :: Map AccountId Money 
                   , choice :: Map ChoiceId ChosenNum
                   , minSlot :: SlotNumber }

data Environment = Environment { slotInterval :: SlotInterval }
  deriving (Eq,Ord,Show,Read)

data Input = IDeposit AccountId Party Integer 
           | IChoice ChoiceId ChosenNum 
           | INotify
  deriving (Eq,Ord,Show,Read)

-- Evaluate a value
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value =
  case value of
    AvailableMoney accId -> M.findWithDefault 0 accId $ account state
    Constant integer -> integer
    NegValue val -> go val
    AddValue lhs rhs -> go lhs + go rhs
    SubValue lhs rhs -> go lhs + go rhs
    ChoiceValue choId defVal -> M.findWithDefault (go defVal) choId $ choice state
    SlotIntervalStart -> fst $ slotInterval env
    SlotIntervalEnd -> snd $ slotInterval env
  where go = evalValue env state

-- Evaluate an observation
evalObservation :: Environment -> State -> Observation -> Bool
evalObservation env state obs =
  case obs of
    AndObs lhs rhs -> goObs lhs && goObs rhs 
    OrObs lhs rhs -> goObs lhs || goObs rhs
    NotObs subObs -> not $ goObs subObs
    ChoseSomething choId -> choId `M.member` choice state
    ValueGE lhs rhs -> goVal lhs >= goVal rhs
    ValueGT lhs rhs -> goVal lhs > goVal rhs
    ValueLT lhs rhs -> goVal lhs < goVal rhs
    ValueLE lhs rhs -> goVal lhs <= goVal rhs
    ValueEQ lhs rhs -> goVal lhs == goVal rhs
    TrueObs -> True
    FalseObs -> False
  where goObs = evalObservation env state
        goVal = evalValue env state

-- Pick the first account with money in it
refundOne :: Map AccountId Money -> Maybe ((Party, Money), Map AccountId Money)
refundOne accounts =
   do ((accId, mon), rest) <- M.minViewWithKey accounts
      if mon > 0
      then return ((accountOwner accId, mon), rest)
      else refundOne rest

-- Obtains the amount of money available an account
moneyInAccount :: Map AccountId Money -> AccountId -> Money
moneyInAccount accs accId = M.findWithDefault 0 accId accs

-- Sets the amount of money available in an account
updateMoneyInAccount :: Map AccountId Money -> AccountId -> Money -> Map AccountId Money
updateMoneyInAccount accs accId mon
  | mon <= 0 = M.delete accId accs
  | otherwise = M.insert accId mon accs

-- Withdraw up to the given amount of money from an account
-- Return the amount of money withdrawn
withdrawMoneyFromAccount :: Map AccountId Money -> AccountId -> Money
                         -> (Money, Map AccountId Money)
withdrawMoneyFromAccount accs accId mon =
  (withdrawnMoney, newAcc)
  where avMoney = moneyInAccount accs accId
        withdrawnMoney = min avMoney mon
        newAvMoney = avMoney - withdrawnMoney
        newAcc = updateMoneyInAccount accs accId newAvMoney

-- Add the given amount of money to an accoun (only if it is positive)
-- Return the updated Map
addMoneyToAccount :: Map AccountId Money -> AccountId -> Money -> Map AccountId Money
addMoneyToAccount accs accId mon
  | mon <= 0 = accs
  | otherwise = updateMoneyInAccount accs accId newAvMoney
  where avMoney = moneyInAccount accs accId
        newAvMoney = avMoney + mon

-- Gives the given amount of money to the given payee
-- Return the appropriate effect and updated Map
giveMoney :: Map AccountId Money -> Payee -> Money -> (ReduceEffect, Map AccountId Money)
giveMoney accs (Party party) mon = (ReduceNormalPay party mon, accs)
giveMoney accs (Account accId) mon = (ReduceNoEffect, newAccs)
  where newAccs = addMoneyToAccount accs accId mon

data ReduceWarning = ReduceNoWarning
                   | ReduceNonPositivePay AccountId Payee Money 
                   | ReducePartialPay AccountId Payee Money Money 
                                    -- ^ src    ^ dest ^ paid ^ expected

data ReduceEffect = ReduceNoEffect
                  | ReduceNormalPay Party Money 

data ReduceError = ReduceAmbiguousSlotInterval

data ReduceResult = Reduced ReduceWarning ReduceEffect State Contract
                  | NotReduced
                  | ReduceError ReduceError

-- Carry a step of the contract with no inputs
reduce :: Environment -> State -> Contract -> ReduceResult
reduce _ state c@RefundAll =
  case refundOne $ account state of
    (Just ((party, money), newAccount)) ->
       let newState = state { account = newAccount } in
       Reduced ReduceNoWarning (ReduceNormalPay party money) newState c
    Nothing ->
       NotReduced
reduce env state (Pay accId payee val nc) =
  if mon <= 0
  then Reduced (ReduceNonPositivePay accId payee mon) ReduceNoEffect state nc
  else Reduced noMonWarn payEffect (state {account = finalAccs}) nc
  where mon = evalValue env state val
        (paidMon, newAccs) = withdrawMoneyFromAccount (account state) accId mon
        noMonWarn = if paidMon < mon
                    then ReducePartialPay accId payee paidMon mon
                    else ReduceNoWarning
        (payEffect, finalAccs) = giveMoney newAccs payee paidMon 
reduce env state (If obs cont1 cont2) =
  Reduced ReduceNoWarning ReduceNoEffect state nc
  where nc = if evalObservation env state obs
             then cont1
             else cont2
reduce env state (When _ timeout c) =
  if endSlot < timeout
  then NotReduced
  else if startSlot >= timeout
       then Reduced ReduceNoWarning ReduceNoEffect state c
       else ReduceError ReduceAmbiguousSlotInterval
  where startSlot = fst $ slotInterval env
        endSlot = snd $ slotInterval env

data ApplyError = ApplyNoMatch

data ApplyResult = Applied State Contract
                 | ApplyError ApplyError

-- Apply a single Input to the contract (assumes the contract is reduced)
applyCases :: Environment -> State -> Input -> [Case] -> ApplyResult
applyCases env state (IDeposit accId1 party1 mon1) (Case (Deposit accId2 party2 val2) nc:_)
  | accId1 == accId2 && party1 == party2 && mon1 == mon2 = Applied newState nc
  where mon2 = evalValue env state val2
        accs = account state
        newAccs = addMoneyToAccount accs accId1 mon1
        newState = state { account = newAccs }
applyCases _ state (IChoice choId1 cho1) (Case (Choice choId2 bounds2) nc:_)
  | choId1 == choId2 && inBounds cho1 bounds2 = Applied newState nc
  where newState = state { choice = M.insert choId1 cho1 $ choice state }
applyCases env state INotify (Case (Notify obs) nc :_)
  | evalObservation env state obs = Applied state nc
applyCases env state act (_:t) = applyCases env state act t
applyCases _ _ _ [] = ApplyError ApplyNoMatch

apply :: Environment -> State -> Input -> Contract -> ApplyResult
apply env state act (When cases _ _) = applyCases env state act cases
apply _ _ _ _ = ApplyError ApplyNoMatch

-- ToDo: need to trim interval and check is valid (higher than minSlot, and ascendent)
-- ToDo: check IDeposit and IChoice have appropriate signatures

