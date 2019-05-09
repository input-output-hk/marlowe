module Semantics where

import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)

data SetupContract = SetupContract {
    bounds :: Bounds,
    contract :: Contract
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
initialiseState (SetupContract { bounds = inpBounds
                               , contract = inpContract }) =
  State { stateChoices = M.empty
        , stateBounds = inpBounds
        , stateContracts = [(0, inpContract)] }

data Environment =
  Environment { envChoices :: Map ChoiceId Integer
              , envBounds :: Bounds
              , envOracles :: Map OracleId Integer }

initEnvironment :: Input -> State -> Environment
initEnvironment = initEnvironment

contractLifespan :: Contract -> Integer
contractLifespan contract = case contract of
    Null -> 0
    Commit _ _ timeout contract1 contract2 ->
        maximum [timeout, contractLifespan contract1, contractLifespan contract2]
    Pay _ _ -> 0
    All shares ->   let contractsLifespans = fmap (contractLifespan . snd) shares
                    in maximum contractsLifespans
    -- TODO simplify observation and check for always true/false cases
    If observation contract1 contract2 ->
        max (contractLifespan contract1) (contractLifespan contract2)
    When cases timeout contract -> let
        contractsLifespans = fmap (\(Case obs cont) -> contractLifespan cont) cases
        in maximum (timeout <| contractLifespan contract <| contractsLifespans)
    While observation timeout contract1 contract2 ->
        maximum [timeout, contractLifespan contract1, contractLifespan contract2]

-- Evaluate a value
evalValue :: SlotNumber -> Environment -> Value -> Integer
evalValue slotNumber env value = case value of
    Constant i -> i
    AvailableMoney -> error "Take from state?" -- TODO
    AddValue lhs rhs -> go lhs + go rhs
    SubValue lhs rhs -> go lhs - go rhs
    ChoiceValue choiceId value ->
        fromMaybe (go value) $ M.lookup choiceId (envChoices env)
    OracleValue oracleId value ->
        fromMaybe (go value) $ M.lookup oracleId (envOracles env)
    CurrentSlot -> slotNumber
  where go = evalValue slotNumber env

-- Evaluate an observation
evalObservation :: SlotNumber -> Environment -> Observation -> Bool
evalObservation slotNumber env obs = case obs of
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
  where go = evalObservation slotNumber env
        goValue  = evalValue slotNumber env

-- Decides whether something has expired
isExpired :: SlotNumber -> SlotNumber -> Bool
isExpired currSlotNumber expirationSlotNumber = currSlotNumber >= expirationSlotNumber


