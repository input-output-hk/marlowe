module Semantics where

import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Map (Map)

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
    Commit Party Value Timeout Contract Contract |
    Pay Party Value |
    All (NonEmpty (Value, Contract)) |
--    Catch Contract Contract | 
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
                   , inputOracleValues :: (Map OracleId Integer)
                   , inputChoices :: (Map ChoiceId Integer) }
               deriving (Eq, Ord, Show, Read)

data InputCommand = Perform (NonEmpty ActionId)
                  | Evaluate
               deriving (Eq, Ord, Show, Read)


data State = State { stateChoices :: Map ChoiceId Integer
                   , stateBounds :: Bounds
                   , stateContract :: [(Money, Contract)] }
               deriving (Eq, Ord, Show, Read)
contractLifespan :: Contract -> Integer
contractLifespan contract = case contract of
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

