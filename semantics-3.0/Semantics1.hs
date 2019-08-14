{-# LANGUAGE StrictData     #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE NamedFieldPuns     #-}
module Semantics1 where

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
}
               deriving (Eq, Ord, Show, Read)

data Bounds = Bounds {
    oracleBounds :: Map OracleId Bound,
    choiceBounds :: Map ChoiceId Bound
}
               deriving (Eq, Ord, Show, Read)

type PubKey = Integer
type Party = PubKey
type NumChoice = Integer
type Timeout = Integer
type SlotNumber = Integer
type ActionId = Integer
type Money = Integer

data Contract =
    Null |
    Commit Party Value Timeout Contract Contract |
    Pay Party Value |
    All (NonEmpty (Value, Contract)) |
    If Observation Contract Contract |
    When (NonEmpty Case) Timeout Contract |
    While Observation Timeout Contract Contract
--    Let LetLabel Contract Contract |
--    Use LetLabel
               deriving (Eq, Ord, Show, Read)

data Case = Case Observation Contract
               deriving (Eq, Ord, Show, Read)

data ChoiceId = ChoiceId NumChoice Party
               deriving (Eq, Ord, Show, Read)

data OracleId = OracleId PubKey
               deriving (Eq, Ord, Show, Read)

type Bound = NonEmpty (Integer, Integer) -- lower/upper bounds are included

data Value = Constant Integer |
             AvailableMoney |
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
                  | Evaluate
               deriving (Eq, Ord, Show, Read)


data State = State { stateChoices :: Map ChoiceId Integer
                   , stateBounds :: Bounds
                   , stateContracts :: [(Money, Contract)] }
               deriving (Eq, Ord, Show, Read)

emptyBounds :: Bounds
emptyBounds = Bounds { oracleBounds = M.empty
                     , choiceBounds = M.empty }

initialiseState :: SetupContract -> State
initialiseState (SetupContract { setupBounds = inpBounds
                               , setupContract = inpContract }) =
  State { stateChoices = M.empty
        , stateBounds = inpBounds
        , stateContracts = [(0, inpContract)] }

data Environment =
  Environment { envSlotNumber :: SlotNumber
              , envChoices :: Map ChoiceId Integer
              , envBounds :: Bounds
              , envOracles :: Map OracleId Integer
              , envAvailableMoney :: Money }

initEnvironment :: SlotNumber -> Input -> State -> (Maybe (Money -> Environment))
initEnvironment slotNumber (Input { inputOracleValues = inOra
                                  , inputChoices = inCho })
                (State { stateChoices = staCho
                       , stateBounds = staBou })
  | M.null $ M.intersection inCho staCho = Just $
       (\availMoney ->
          Environment { envSlotNumber = slotNumber
                      , envChoices = M.union inCho staCho
                      , envBounds = staBou
                      , envOracles = inOra
                      , envAvailableMoney = availMoney })
  | otherwise = Nothing

intersperseAndWrap :: a -> [a] -> [a]
intersperseAndWrap x [] = [x]
intersperseAndWrap x (h:t) = (x:h:intersperseAndWrap x t)

-- From monad-loops package
-- |Compose a list of monadic actions into one action.  Composes using
-- ('>=>') - that is, the output of each action is fed to the input of
-- the one after it in the list.
concatM :: (Monad m) => [a -> m a] -> (a -> m a)
concatM fs = foldr (>=>) return fs

-- ToDo: Check signatures for choices
applyInput :: SlotNumber -> Signatoires -> Input -> State -> Maybe State
applyInput sn s inp@(Input { inputCommand }) st =
  do envF <- initEnvironment sn inp st
     let reduceOnce = reduceState envF
     let performOnce = applyCommandState s envF
     case inputCommand of
       Evaluate -> reduceOnce st
       Perform actions -> let performList = map (performOnce) (NE.toList actions) in
                          let reducePerformList = intersperseAndWrap reduceOnce performList in
                          concatM reducePerformList st

applyCommandState :: Signatoires -> (Money -> Environment) -> ActionId -> State -> Maybe State
applyCommandState s envF aid (st@State { stateContracts }) =
  do newStateContracts <- applyCommand s envF aid stateContracts
     return $ st { stateContracts = newStateContracts }

reduceState :: (Money -> Environment) -> State -> Maybe State
reduceState envF st@(State { stateContracts }) =
  do x <- traverse (\(m, c) -> reduce (envF m) c) stateContracts
     return $ st { stateContracts = concat (map NE.toList x) }

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

reduce :: Environment -> Contract -> Maybe (NonEmpty (Money, Contract))
reduce env contract = case contract of
    Null -> Just $ (availableMoney, Null) :| []
    Commit _ _ _ _ _ -> Just $ (availableMoney, contract) :| []
    Pay _ _ -> Just $ (availableMoney, contract) :| []
    All shares -> let
        eshares = NE.map (\(v, sc) -> (evalValue env v, sc)) shares
        total = foldr ((+) . fst) 0 eshares in
        if total == availableMoney
        then do
            fl <- forM eshares $ \(sv, sc) -> reduce (env { envAvailableMoney = sv }) sc
            return $ join fl
        else Nothing
    If obs cont1 cont2 ->
        if evalObservation env obs then go cont1 else go cont2
    When cases timeout timeoutCont ->
        if isExpired slotNumber timeout
        then go timeoutCont
        else case find (\(Case obs _) -> evalObservation env obs) (NE.toList cases) of
                Nothing -> Just $ (envAvailableMoney env, contract) :| []
                Just (Case _ sc) -> go sc
    While obs timeout contractWhile contractAfter ->
        if (isExpired slotNumber timeout) || (not $ evalObservation env obs)
        then go contractAfter
        else do l <- go contractWhile
                return $ NE.map (\(v, sc) -> (v, While obs timeout sc contractAfter)) l
  where slotNumber = envSlotNumber env
        availableMoney = envAvailableMoney env
        go = reduce env

type Signatoires = Set Party

applyCommand :: Signatoires -> (Money -> Environment) -> ActionId -> [(Money, Contract)] -> Maybe [(Money, Contract)]
applyCommand _ _ _ [] = Nothing
applyCommand s f aid ((hm, hc):t)
  | aid < 1 = Nothing
  | aid == 1 = do x <- applyCommandRec s (f hm) hc
                  return (x:t)
  | otherwise = do x <- applyCommand s f (aid + 1) t
                   return ((hm, hc):x)

applyCommandRec :: Signatoires -> Environment -> Contract -> Maybe (Money, Contract)
applyCommandRec signatories env contract = case contract of
    Null -> Nothing
    Commit party v _ cont _
        | party `S.member` signatories -> Just (availableMoney + evalValue env v, cont)
        | otherwise -> Nothing
    Pay party val
        | party `S.member` signatories && availableMoney >= ev -> Just (availableMoney - ev, Null)
        | otherwise -> Nothing
        where ev = evalValue env val
    All _ -> Nothing
    If _ _ _ -> Nothing
    When _ _ _ -> Nothing
    While obs timeout contractWhile contractAfter -> do
        (money, cont) <- applyCommandRec signatories env contractWhile
        return (money, While obs timeout cont contractAfter)
  where availableMoney = envAvailableMoney env

-- Evaluate a value
evalValue :: Environment -> Value -> Integer
evalValue env value = case value of
    Constant i -> i
    AvailableMoney -> envAvailableMoney env
    AddValue lhs rhs -> go lhs + go rhs
    SubValue lhs rhs -> go lhs - go rhs
    ChoiceValue choiceId val ->
        fromMaybe (go val) $ M.lookup choiceId (envChoices env)
    OracleValue oracleId val ->
        fromMaybe (go val) $ M.lookup oracleId (envOracles env)
    CurrentSlot -> envSlotNumber env
  where go = evalValue env

-- Evaluate an observation
evalObservation :: Environment -> Observation -> Bool
evalObservation env obs = case obs of
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
  where go = evalObservation env
        goValue  = evalValue env

-- Decides whether something has expired
isExpired :: SlotNumber -> SlotNumber -> Bool
isExpired currSlotNumber expirationSlotNumber = currSlotNumber >= expirationSlotNumber

-- Calculates an upper bound for the maximum lifespan of a contract
contractLifespan :: Contract -> Integer
contractLifespan contract = case contract of
    Null -> 0
    Commit _ _ timeout contract1 contract2 ->
        maximum [timeout, contractLifespan contract1, contractLifespan contract2]
    Pay _ _ -> 0
    All shares ->   let contractsLifespans = fmap (contractLifespan . snd) shares
                    in maximum contractsLifespans
    -- TODO simplify observation and check for always true/false cases
    If _ contract1 contract2 ->
        max (contractLifespan contract1) (contractLifespan contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespan cont) cases
        in maximum (timeout <| contractLifespan subContract <| contractsLifespans)
    While _ timeout contract1 contract2 ->
        maximum [timeout, contractLifespan contract1, contractLifespan contract2]

expireContract :: SlotNumber -> Contract -> Contract
expireContract slotNumber contract = case contract of
    Null -> Null
    Commit _ _ timeout _ cont2 ->
        if isExpired slotNumber timeout then go cont2 else contract
    Pay _ _ -> contract
    All shares -> All $ fmap (\(v, c) -> (v, go c)) shares
    If obs cont1 cont2 -> If obs (go cont1) (go cont2)
    When cases timeout timeoutCont -> let
        reducedTimeoutCont = go timeoutCont
        updatedCases = fmap (\(Case obs cont) -> Case obs $ go cont) cases
        in if isExpired slotNumber timeout
           then reducedTimeoutCont
           else When updatedCases timeout reducedTimeoutCont

    While obs timeout contractWhile contractAfter ->
        if isExpired slotNumber timeout
            then go contractAfter
            else While obs timeout (go contractWhile) (go contractAfter)
  where go = expireContract slotNumber

inferActions :: Contract -> [Contract]
inferActions contract = let
    inner = case contract of
        Null -> []
        Commit _ _ _ _ _ -> [contract]
        Pay _ _ -> [contract]
        All shares -> foldMap (\(_, c) -> inferActions c) (NE.toList shares)
        If _ _ _ -> [contract]
        When _ _ _ -> []
        While _ _ contractWhile _ -> inferActions contractWhile
    in inner

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
escrow = Commit alice (Constant 450) 10
    (When (Case majorityAgrees (Pay bob AvailableMoney) :|
           [Case majorityDisagrees (Pay alice AvailableMoney)])
        90 (Pay alice AvailableMoney))
    Null
