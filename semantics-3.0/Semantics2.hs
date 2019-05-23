{-# LANGUAGE StrictData     #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE NamedFieldPuns     #-}
module Semantics2 where

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

type CommitId = Integer
type PubKey = Integer
type Party = PubKey
type NumChoice = Integer
type Timeout = Integer
type SlotNumber = Integer
type ActionId = Integer
type Money = Integer
type LetLabel = Integer


data Contract =
    Null |
    Commit CommitId Party Value Timeout Contract Contract |
    Pay CommitId CommitId Value Timeout Contract Contract | -- transfer Value money from CommitId to CommitId
    Redeem CommitId | -- withdraw everything left in CommitId
    Both Contract Contract |
    If Observation Contract Contract |
    When [Case] Timeout Contract | -- empty Case list for 'after timeout' semantics
    While Observation Timeout Contract Contract
    -- Let LetLabel Contract Contract |
    -- Use LetLabel
               deriving (Eq, Ord, Show, Read)

data Case = Case Observation Contract
               deriving (Eq, Ord, Show, Read)

data ChoiceId = ChoiceId NumChoice Party
               deriving (Eq, Ord, Show, Read)

data OracleId = OracleId PubKey
               deriving (Eq, Ord, Show, Read)

type Bound = NonEmpty (Integer, Integer) -- lower/upper bounds are included

data Value = Constant Integer |
             AvailableMoney CommitId |
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

data InputCommand = Perform (NonEmpty ActionId)
                  | Withdraw Party Money
                  | Evaluate
               deriving (Eq, Ord, Show, Read)


data State = State { stateChoices :: Map ChoiceId Integer
                   , stateBounds  :: Bounds
                   , stateCommits :: Map CommitId Party
                   , stateBalance :: Map CommitId Integer
                   , stateUnclaimedRedeems :: Map Party Money
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
        , stateCommits = M.empty
        , stateBalance = M.empty
        , stateUnclaimedRedeems = M.empty
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


-- ToDo: Check signatures for choices
applyInput :: SlotNumber -> Signatoires -> Input -> State -> Contract -> Maybe (State, Contract)
applyInput slotNumber signatoires input@Input{..} state contract = do
    env <- initEnvironment slotNumber input state
    case inputCommand of
        Withdraw party amount -> do
            (st, c) <- reduce env state contract
            let redeems = stateUnclaimedRedeems st
            case M.lookup party redeems of
                Just val | val > amount -> let
                    updatedState = st {
                            stateUnclaimedRedeems = M.adjust (\v -> v - amount) party redeems
                        }
                    in return (updatedState, c)
        Evaluate -> reduce env state contract
        Perform actions -> let
            perform (st, cont) actionId = performAction env st actionId cont
            in foldM perform (state, contract) actions


performAction :: Environment -> State -> ActionId -> Contract -> Maybe (State, Contract)
performAction env state actionId contract = do
    (st, c) <- reduce env state contract
    case transform st actionId 0 c of
        Left _ -> Nothing
        Right r -> r
  where
    transform :: State -> ActionId -> ActionId -> Contract -> Either Integer (Maybe (State, Contract))
    transform state actionId idx contract
        | idx < actionId = case contract of
            Both c1 c2 -> case transform state actionId (idx + 1) c1 of
                Left idx -> case transform state actionId (idx + 1) c2 of
                    Right (Just (st, c)) -> Right (Just (st, Both c1 c))
                    left -> left
                Right (Just (st, c)) -> Right (Just (st, Both c c2))
            While obs timeout contractWhile fail ->
                case transform state actionId (idx + 1) contractWhile of
                    Right (Just (st, c)) -> Right (Just (st, While obs timeout c fail))
                    left -> left
            _ -> Left idx
        | idx == actionId = case contract of
            Commit commitId party value timeout contract fail -> do
                let evaluatedValue = evalValue env state value
                let commits = stateCommits state
                let balances = stateBalance state
                let updatedState = state {
                    stateCommits = M.insert commitId party commits,
                    stateBalance = M.alter (\am -> Just $ fromMaybe 0 am + evaluatedValue) commitId balances
                }
                Right $ Just (state, contract)
            Pay from to value timeout contract fail -> do
                let evaluatedValue = evalValue env state value
                let commits = stateCommits state
                let balances = stateBalance state
                let fromBalance = balances M.! from
                if fromBalance >= evaluatedValue then let
                    newBalances = M.adjust (\amount -> amount - evaluatedValue) from $
                        M.adjust (\amount -> amount + evaluatedValue) to balances
                    updatedState = state { stateBalance = newBalances }
                    in Right $ Just (state, contract)
                else Right Nothing
        | otherwise = Left idx

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

reduce :: Environment -> State -> Contract -> Maybe (State, Contract)
reduce env state contract = case contract of
    Null -> Just (state, Null)
    Commit{} -> Just (state, contract)
    Pay{} -> Just (state, contract)
    Redeem _ -> Just (state, contract)
    Both c1 c2 -> Just (state, contract)
    If obs cont1 cont2 ->
        if evalObservation env state obs then go cont1 else go cont2
    When cases timeout timeoutCont ->
        if isExpired slotNumber timeout
        then go timeoutCont
        else case find (\(Case obs _) -> evalObservation env state obs) cases of
                Nothing -> Just (state, contract)
                Just (Case _ sc) -> go sc
    While obs timeout contractWhile contractAfter ->
        if isExpired slotNumber timeout || not (evalObservation env state obs)
        then go contractAfter
        else do l <- go contractWhile
                return $ fmap (\sc -> While obs timeout sc contractAfter) l
  where slotNumber = envSlotNumber env
        go = reduce env state

type Signatoires = Set Party

-- Evaluate a value
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value = case value of
    Constant i -> i
    AvailableMoney commitId -> stateBalance state M.! commitId
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
    ChoseSomething choiceId -> choiceId `M.member` (envChoices env)
    OracleValueProvided oracleId -> oracleId `M.member` (envOracles env)
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
    Null -> 0
    Commit _ _ _ timeout contract1 contract2 ->
        maximum [timeout, contractLifespan contract1, contractLifespan contract2]
    Pay{} -> 0
    Redeem{} -> 0
    Both c1 c2 -> contractLifespan c1 `max` contractLifespan c2
    -- TODO simplify observation and check for always true/false cases
    If _ contract1 contract2 ->
        max (contractLifespan contract1) (contractLifespan contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespan cont) cases
        in maximum (timeout : contractLifespan subContract : contractsLifespans)
    While _ timeout contract1 contract2 ->
        maximum [timeout, contractLifespan contract1, contractLifespan contract2]

inferActions :: Environment -> State -> Contract -> [Contract]
inferActions env state contract = case contract of
    Null -> []
    Commit{} -> [contract]
    Pay{} -> [contract]
    Redeem{} -> error "Should not happen. Looks like you infer action for non-reduced contract. Try reduce it first. Redeems should be reduced automatically"
    Both c1 c2 -> go c1 ++ go c2
    If _ c1 c2 -> error "Should not happen. Looks like you infer action for non-reduced contract. Try reduce it first. If should be reduced automatically"
    When{} -> []
    While _ _ contractWhile _ -> go contractWhile
  where go = inferActions env state

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
escrow = Commit alice alice (Constant 450) 10
    (When  [ Case majorityAgrees (Pay alice bob (AvailableMoney alice) 90 (Redeem bob) (Redeem bob))
           , Case majorityDisagrees (Redeem alice) ]
        90 (Redeem alice))
    Null
