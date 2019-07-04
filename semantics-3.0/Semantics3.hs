{-# LANGUAGE StrictData     #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE NamedFieldPuns     #-}
module Semantics3 where

import Control.Monad
import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NE
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Control.Monad ((>=>))

data SetupContract = SetupContract {
    setupBounds :: Bounds,
    setupContract :: Contract
} deriving (Eq, Ord, Show, Read)

data Bounds = Bounds {
    oracleBounds :: Map OracleId Bound,
    choiceBounds :: Map ChoiceId Bound
}
               deriving (Eq, Ord, Show, Read)

newtype AccountId = AccountId Integer deriving (Eq, Ord, Show, Read)
type Party = Integer
type NumChoice = Integer
type Timeout = Integer
type SlotNumber = Integer
type ActionId = Integer
type Money = Integer
type LetLabel = Integer
newtype Signature = Signature Party deriving (Eq, Ord, Show, Read)

data Payee = Account AccountId Party | Party Party deriving (Eq, Ord, Show, Read)
data Commitment = Commitment AccountId Party Value deriving (Eq, Ord, Show, Read)

data Contract =
    RedeemAll |
    CommitAll [Commitment] Timeout Contract Contract |
    Pay AccountId Payee Value Contract |
    If Observation Contract Contract |
    When [Case] Timeout Contract
               deriving (Eq, Ord, Show, Read)

data Case = Case Observation Contract
               deriving (Eq, Ord, Show, Read)

data ChoiceId = ChoiceId NumChoice Party
               deriving (Eq, Ord, Show, Read)

data OracleId = OracleId Party
               deriving (Eq, Ord, Show, Read)

type Bound = NonEmpty (Integer, Integer) -- lower/upper bounds are included

data Value = Constant Integer |
             AvailableMoney AccountId |
             AddValue Value Value |
             SubValue Value Value |
             ChoiceValue ChoiceId Value |
             OracleValue OracleId Value |
             CurrentSlot -- ToDo: think about slot intervals
               deriving (Eq, Ord, Show, Read)

data Observation = AndObs Observation Observation |
                   OrObs Observation Observation |
                   NotObs Observation |
                   ChoseSomething ChoiceId |
                   OracleValueProvided OracleId |
                   ValueGE Value Value |
                   ValueGT Value Value |
                   ValueLT Value Value |
                   ValueLE Value Value |
                   ValueEQ Value Value |
                   TrueObs |
                   FalseObs
               deriving (Eq, Ord, Show, Read)

data Input = Input { inputCommand :: InputCommand
                   , inputOracleValues :: Map OracleId Integer
                   , inputChoices :: Map ChoiceId Integer }
               deriving (Eq, Ord, Show, Read)

data InputCommand = Deposit (NonEmpty (ActionId, Signature, Money))
                  | Redeem Signature AccountId
                  | Evaluate
               deriving (Eq, Ord, Show, Read)


data State = State { stateChoices :: Map ChoiceId Integer
                   , stateBounds  :: Bounds
                   , stateBalances :: Map AccountId (Party, Money)
                   , stateContractTimeout :: Timeout
                   }
               deriving (Eq, Ord, Show, Read)

emptyBounds :: Bounds
emptyBounds = Bounds { oracleBounds = M.empty
                     , choiceBounds = M.empty }

initialiseState :: SetupContract -> State
initialiseState SetupContract{..} =
  State { stateChoices = M.empty
        , stateBounds = setupBounds
        , stateBalances = M.empty
        , stateContractTimeout = contractLifespan setupContract
        }

data Environment =
  Environment { envSlotNumber :: SlotNumber
              , envChoices :: Map ChoiceId Integer
              , envBounds :: Bounds
              , envOracles :: Map OracleId Integer
              }

initEnvironment :: SlotNumber -> Input -> State -> Maybe Environment
initEnvironment slotNumber Input{..} State {..}
  | M.null $ M.intersection inputChoices stateChoices = Just $
          Environment { envSlotNumber = slotNumber
                      , envChoices = M.union inputChoices stateChoices
                      , envBounds = stateBounds
                      , envOracles = inputOracleValues
                      }
  | otherwise = Nothing


applyInput :: SlotNumber -> Integer -> Integer -> Input -> State -> Contract -> Maybe (State, Contract)
applyInput slotNumber beforeBalance afterBalance input@Input{..} state@State{..} contract = do
    env <- initEnvironment slotNumber input state
    case eval env state contract of
        Just (st, cont) -> case (inputCommand, cont) of
            (Redeem (Signature party) accountId, RedeemAll) -> do
                case M.lookup accountId stateBalances of
                    Just (p, val) | p == party && beforeBalance - val == afterBalance -> let
                        updatedState = st { stateBalances = M.insert accountId (party, 0) stateBalances }
                        in return (updatedState, RedeemAll)
                    _ -> Nothing
            (Evaluate, cont) | beforeBalance == afterBalance -> Just (st, cont)
            (Deposit actions, CommitAll commitments _ _ _) -> undefined {- let
                s = sum $ fmap (\(_, _, value) -> evalValue env st value) actions
                len = length commitments
                valid = all (\(id, (Signature p), _) -> 0 <= id && id < len && p == commitments ) actions
                valid = -}
        Nothing -> Nothing

-- How much everybody pays or receives in transaction
type TransactionOutcomes = M.Map Party Integer

emptyOutcome :: TransactionOutcomes
emptyOutcome = M.empty

isEmptyOutcome :: TransactionOutcomes -> Bool
isEmptyOutcome trOut = all (== 0) trOut

-- Adds a value to the map of outcomes
addOutcome :: Party -> Integer -> TransactionOutcomes -> TransactionOutcomes
addOutcome party diffValue trOut = M.insert party newValue trOut
  where newValue = case M.lookup party trOut of
                     Just value -> value + diffValue
                     Nothing -> diffValue

-- Add two transaction outcomes together
combineOutcomes :: TransactionOutcomes -> TransactionOutcomes -> TransactionOutcomes
combineOutcomes = M.unionWith (+)

eval :: Environment -> State -> Contract -> Maybe (State, Contract)
eval env state@State{..} contract = case contract of
    RedeemAll -> Just (state, RedeemAll)
    CommitAll _ timeout _ fail ->
        if isExpired slotNumber timeout
        then go fail
        else Just (state, contract)
    Pay from to value cont -> do
        let evaluatedValue = evalValue env state value
        case M.lookup from stateBalances of
            Just (_, amount) | 0 <= evaluatedValue && evaluatedValue <= amount ->
                case to of
                    Account accId party -> let
                        reduceFromAccount = M.adjust (\(party, amount) -> (party, amount - evaluatedValue)) from stateBalances
                        newBalances = M.alter (\v -> case v of
                            Just (p, balance) -> Just (p, balance + evaluatedValue)
                            Nothing -> Just (party, evaluatedValue)) accId reduceFromAccount
                        updatedState = state { stateBalances = newBalances }
                        in eval env updatedState cont
                    Party party -> undefined -- todo
            _ -> Nothing
    If obs cont1 cont2 ->
        if evalObservation env state obs then go cont1 else go cont2
    When cases timeout timeoutCont ->
        if isExpired slotNumber timeout
        then go timeoutCont
        else case find (\(Case obs _) -> evalObservation env state obs) cases of
                Nothing -> Just (state, contract)
                Just (Case _ sc) -> go sc
  where slotNumber = envSlotNumber env
        go = eval env state

type Signatoires = Set Party

getCommitBalance :: AccountId -> State -> Money
getCommitBalance commitId state = case M.lookup commitId (stateBalances state) of
    Just (_, balance) -> balance
    Nothing -> 0

-- Evaluate a value
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value = case value of
    Constant i -> i
    AvailableMoney commitId -> getCommitBalance commitId state
    AddValue lhs rhs -> go lhs + go rhs
    SubValue lhs rhs -> go lhs - go rhs
    ChoiceValue choiceId val ->
        fromMaybe (go val) $ M.lookup choiceId (envChoices env)
    OracleValue oracleId val ->
        fromMaybe (go val) $ M.lookup oracleId (envOracles env)
    CurrentSlot -> envSlotNumber env
  where go = evalValue env state

-- Evaluate an observation
evalObservation :: Environment -> State -> Observation -> Bool
evalObservation env state obs = case obs of
    AndObs lhs rhs -> go lhs && go rhs
    OrObs lhs rhs -> go lhs || go rhs
    NotObs o -> not (go o)
    ChoseSomething choiceId -> choiceId `M.member` envChoices env
    OracleValueProvided oracleId -> oracleId `M.member` envOracles env
    ValueGE lhs rhs -> goValue lhs >= goValue rhs
    ValueGT lhs rhs -> goValue lhs > goValue rhs
    ValueLT lhs rhs -> goValue lhs < goValue rhs
    ValueLE lhs rhs -> goValue lhs <= goValue rhs
    ValueEQ lhs rhs -> goValue lhs == goValue rhs
    TrueObs -> True
    FalseObs -> False
  where go = evalObservation env state
        goValue  = evalValue env state

-- Decides whether something has expired
isExpired :: SlotNumber -> SlotNumber -> Bool
isExpired currSlotNumber expirationSlotNumber = currSlotNumber >= expirationSlotNumber

-- Calculates an upper bound for the maximum lifespan of a contract
contractLifespan :: Contract -> Integer
contractLifespan contract = case contract of
    RedeemAll -> 0
    CommitAll _ timeout contract1 contract2 ->
        maximum [timeout, contractLifespan contract1, contractLifespan contract2]
    Pay _ _ _ cont -> contractLifespan cont
    -- TODO simplify observation and check for always true/false cases
    If _ contract1 contract2 ->
        max (contractLifespan contract1) (contractLifespan contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespan cont) cases
        in maximum (timeout : contractLifespan subContract : contractsLifespans)

alice, bob, carol :: Party
alice = 1
bob = 2
carol = 3

(|||) :: Observation -> Observation -> Observation
(|||) = OrObs

(&&&) :: Observation -> Observation -> Observation
(&&&) = AndObs

(===) :: Value -> Value -> Observation
(===) = ValueEQ

choseThis :: NumChoice -> ChoiceId -> Observation
choseThis choice choiceId  = (ChoiceValue choiceId (Constant 0) === Constant choice)

majority :: NumChoice -> Observation
majority choice = (chose (ChoiceId 1 alice) &&& (chose (ChoiceId 2 bob) ||| chose (ChoiceId 3 carol)))
    ||| (chose (ChoiceId 2 bob) &&& chose (ChoiceId 3 carol))
  where chose = choseThis choice

-- party1 and (party2 or party3) or (party2 and party3)
majorityAgrees :: Observation
majorityAgrees = majority 1

majorityDisagrees :: Observation
majorityDisagrees = majority 2

escrow :: Contract
escrow = CommitAll [Commitment (AccountId alice) alice (Constant 450)] 10
    (When  [ Case majorityAgrees
                (Pay (AccountId alice) (Party bob)
                        (AvailableMoney $ AccountId alice) RedeemAll)
           , Case majorityDisagrees RedeemAll ]
        90 RedeemAll)
    RedeemAll

zeroCouponBondGuaranteed :: Party -> Party -> Party -> Integer -> Integer -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    -- guarantor commits a 'guarantee' before startDate
    CommitAll [ Commitment (AccountId 1) investor (Constant (notional - discount))
              , Commitment (AccountId 2) guarantor (Constant notional) ] startDate
        (When [] startDate
            (Pay (AccountId 1) (Party issuer) (AvailableMoney $ AccountId 1)
                (CommitAll [ Commitment (AccountId 3) issuer (Constant notional) ] maturityDate
                    -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                    (Pay (AccountId 3) (Party investor) (AvailableMoney $ AccountId 3) RedeemAll) -- investor can collect his money
                    -- pay from the guarantor otherwise
                    (Pay (AccountId 2) (Party investor) (AvailableMoney $ AccountId 2) RedeemAll)
                )
            )
        )
        RedeemAll -- investor or guarantor didn't commit, redeem money and finish
