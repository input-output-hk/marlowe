{-# LANGUAGE StrictData     #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE NamedFieldPuns     #-}
module Semantics where

import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NE
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)

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

initEnvironment :: SlotNumber -> Input -> State -> Money -> Maybe Environment
initEnvironment slotNumber (Input { inputOracleValues = inOra
                                  , inputChoices = inCho })
                (State { stateChoices = staCho
                       , stateBounds = staBou }) availMoney
  | M.null $ M.intersection inCho staCho = Just $
       Environment { envSlotNumber = slotNumber
                   , envChoices = M.union inCho staCho
                   , envBounds = staBou
                   , envOracles = inOra
                   , envAvailableMoney = availMoney }
  | otherwise = Nothing

nonEmptyConcatJustMap :: (x -> Maybe (NonEmpty y)) -> NonEmpty x -> Maybe (NonEmpty y)
nonEmptyConcatJustMap f (h :| t) =
  do (fhh :| fht) <- f h
     ft <- mapM ((NE.toList <$>) . f) t
     return (fhh :| (fht ++ (concat ft)))

reduce :: Environment -> Contract -> Maybe (NonEmpty (Money, Contract))
reduce env Null = Just ((envAvailableMoney env, Null) :| [])
reduce env (c@(Commit _ _ _ _ _)) = Just ((envAvailableMoney env, c) :| [])
reduce env (c@(Pay _ _)) = Just ((envAvailableMoney env, c) :| [])
reduce env (All shares) =
  let eshares = NE.map (\(v, sc) -> (evalValue env v, sc)) shares in
  let total = (sum $ NE.toList $ NE.map fst $ eshares) in
  if total == envAvailableMoney env
  then nonEmptyConcatJustMap
         (\(sv, sc) ->
            reduce (env { envAvailableMoney = sv }) sc) eshares
  else Nothing
reduce env (If obs cont1 cont2) =
  if evalObservation env obs
  then reduce env cont1
  else reduce env cont2
reduce env (c@(When cases timeout timeoutCont)) =
  if isExpired (envSlotNumber env) timeout
  then reduce env timeoutCont
  else case find (\(Case obs _) -> evalObservation env obs) (NE.toList cases) of
         Nothing -> Just ((envAvailableMoney env, c) :| [])
         Just (Case _ sc) -> reduce env sc
reduce env (While obs timeout contractWhile contractAfter) =
  if (isExpired (envSlotNumber env) timeout) || (not $ evalObservation env obs)
  then reduce env contractAfter
  else do l <- reduce env contractWhile
          return $ NE.map (\(v,sc) -> (v, While obs timeout sc contractAfter)) l

applyInput :: Input -> Environment -> Contract -> Maybe Contract
applyInput Input{inputCommand} env contract = case inputCommand of
    Evaluate -> reduceContract env contract
    Perform actions -> undefined -- TODO


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

