module Analysis where

import EqSolve
import Semantics
import Data.List (sort, foldl')
import qualified Data.Map as M

data AnalysisVariable = CurrentBlock
                      | ChoiceAV IdentChoice Person
                      | CommitAmmount IdentCC
                      | ChoiceWasMade IdentChoice Person {- Positive (or zero): it was made; negative: it wasn't -}
                      | CommitExists IdentCC {- Positive (or zero): it exists; negative: it doesn't -}
{-                    | Committer IdentChoice -}
                      | TempVar Integer
                    deriving (Eq,Ord,Show,Read)

generateAV :: Integer -> (Integer, EquationTerm AnalysisVariable)
generateAV x = (x + 1, Var $ TempVar x)

generateEq :: [EquationTerm a] -> [EquationTerm a] -> Logic a
generateEq x y = And [Eq $ LE x y, Eq $ LE y x]

commitExists :: IdentCC -> Logic AnalysisVariable
commitExists x = And [Eq $ LE [Const 0] [Var $ CommitExists x],
                      Eq $ LE [Const 0] [Var $ CommitAmmount x]]

commitDoesNotExist :: IdentCC -> Logic AnalysisVariable
commitDoesNotExist x = Eq $ LE [Var $ CommitExists x] [Const (-1)]

choiceMade :: IdentChoice -> Person -> Logic AnalysisVariable
choiceMade x p = Eq $ LE [Const 0] [Var $ ChoiceWasMade x p]

choiceNotMade :: IdentChoice -> Person -> Logic AnalysisVariable
choiceNotMade x p = Eq $ LE [Var $ ChoiceWasMade x p] [Const (-1)]

choiceIs :: IdentChoice -> Person -> [EquationTerm AnalysisVariable] -> Logic AnalysisVariable
choiceIs x p c = And [choiceMade x p, generateEq c [Var $ ChoiceAV x p]]

moneyToLogic :: Integer -> Money -> (Integer, ([EquationTerm AnalysisVariable], Logic AnalysisVariable))
moneyToLogic idx (AvailableMoney x) = (idx, ([Var $ CommitAmmount x], commitExists x))
moneyToLogic idx (AddMoney x y) = (idx3, (xv ++ yv, nl))
  where
   (idx2, (xv, xl)) = moneyToLogic idx x
   (idx3, (yv, yl)) = moneyToLogic idx2 y
   nl = And [xl,yl]
moneyToLogic idx (ConstMoney x) = (idx, ([Const (fromIntegral x)], And []))
moneyToLogic idx (MoneyFromChoice identChoice person m) =(idx3, ([nv], nl))
  where
    (idx2, (mv, ml)) = moneyToLogic idx m
    (idx3, nv) = generateAV idx2
    nl = Or [And [ml, choiceNotMade identChoice person, generateEq [nv] mv],
             choiceIs identChoice person [nv]]

observationToLogic :: Integer -> Observation -> (Integer, Logic AnalysisVariable)
observationToLogic idx (BelowTimeout x) = (idx, Not $ Eq $ LE [Const (fromIntegral x)] [Var CurrentBlock])
observationToLogic idx (AndObs obs1 obs2) = (idx2, And [l1, l2])
  where
    (idx1, l1) = observationToLogic idx obs1
    (idx2, l2) = observationToLogic idx1 obs2
observationToLogic idx (OrObs obs1 obs2) = (idx2, Or [l1, l2])
  where
    (idx1, l1) = observationToLogic idx obs1
    (idx2, l2) = observationToLogic idx1 obs2
observationToLogic idx (NotObs obs) = (idx1, Not l1)
  where
    (idx1, l1) = observationToLogic idx obs
observationToLogic idx (PersonChoseThis idchoice per cchoice) =
   (idx, choiceIs idchoice per [Const $ fromIntegral cchoice])
observationToLogic idx (PersonChoseSomething idchoice per) = (idx, choiceMade idchoice per)
observationToLogic idx (ValueGE m1 m2) = (idx2, And [l1, l2, Eq $ LE v2 v1])
  where
    (idx1, (v1, l1)) = moneyToLogic idx m1
    (idx2, (v2, l2)) = moneyToLogic idx1 m2
observationToLogic idx TrueObs = (idx, And [])
observationToLogic idx FalseObs = (idx, Or [])

updateStateOS :: (State, OS) -> (AnalysisVariable, Integer) -> (State, OS)
updateStateOS (sta, obs) (CurrentBlock, val) = (sta, obs {blockNumber = fromIntegral val})
updateStateOS (sta@(State {sch = schmap}), obs) (ChoiceAV icho pe, val) =
  (sta{sch = M.insert (icho, pe) (fromIntegral val) schmap}, obs)
updateStateOS (sta@(State {sc = scmap}), obs@(OS {blockNumber = bn})) (CommitAmmount icom, val) =
  (sta {sc = M.insert icom (0, NotRedeemed (fromIntegral val) (bn + 1)) scmap}, obs)
updateStateOS (sta@(State {sch = schmap}), obs) (ChoiceWasMade icho pe, val)
  | val >= 0 = (sta {sch = if (M.member (icho, pe) schmap)
                           then schmap else (M.insert (icho, pe) 0 schmap)}, obs)
  | otherwise = (sta {sch = M.delete (icho, pe) schmap}, obs)
updateStateOS (sta@(State {sc = scmap}), obs@(OS {blockNumber = bn})) (CommitExists icom, val)
  | val >= 0 = (sta {sc = if (M.member icom scmap)
                          then scmap else (M.insert icom (1, NotRedeemed 1 (bn + 1)) scmap)}, obs)
  | otherwise = (sta {sc = M.delete icom scmap}, obs)
updateStateOS (sta, obs) (TempVar _, _) = (sta, obs)

emptyStateOS :: (State, OS)
emptyStateOS = (State {sc = M.empty, sch = M.empty}, OS { random = 0, blockNumber = 0})

satisfyObservation :: Observation -> Maybe (State, OS)
satisfyObservation obs =
  case maybeSols of
    Just sols -> Just $ foldl' updateStateOS emptyStateOS (sort sols)
    Nothing -> Nothing
  where (_, log) = observationToLogic 1 obs
        maybeSols = solveLogic log

 
