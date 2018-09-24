module SmartInputs where

import Semantics

import qualified Data.Set as Set
import qualified Data.Map as Map

-- Combines two input sets assuming they are exclusive
combineInputs :: Input -> Input -> Input
combineInputs Input {cc = cci1, rc = rci1, rp = rpi1, ic = ici1}
              Input {cc = cci2, rc = rci2, rp = rpi2, ic = ici2} =
  Input {cc = Set.union cci1 cci2, rc = Set.union rci1 rci2,
         rp = Map.union rpi1 rpi2, ic = Map.union ici1 ici2}

-- Obtains all the inputs that can be deduced from the remaining contract
-- except choices and expired redeems
getPotentialInputsFromContract :: OS -> Contract -> State -> Input
getPotentialInputsFromContract os (CommitCash idencc per cash _ tim2 _ _) st
  | Map.member idencc (sc st) = emptyInput
  | otherwise = emptyInput {cc = Set.singleton (CC idencc per (evalMoney st os cash) tim2)}
getPotentialInputsFromContract _ (RedeemCC idencc _) st =
  case Map.lookup idencc (sc st) of
    Just (person, NotRedeemed val _) -> emptyInput {rc = Set.singleton (RC idencc person val)}
    _ -> emptyInput
getPotentialInputsFromContract os (Pay idenpay _ pt cash _ _) st =
  emptyInput {rp = Map.singleton (idenpay, pt) (evalMoney st os cash)}
getPotentialInputsFromContract os (Both c1 c2) st
  = combineInputs (getPotentialInputsFromContract os c1 st)
                  (getPotentialInputsFromContract os c2 st)
getPotentialInputsFromContract _ _ _ = emptyInput

-- Obtains all the choices that are checked by an observation (taken as "0")
getUsedChoiceNumbersObs :: State -> Observation -> Input
getUsedChoiceNumbersObs st (PersonChoseThis identch per _)
  | not $ Map.member (identch, per) (sch st) = emptyInput {ic = Map.singleton (identch, per) 0}
  | otherwise = emptyInput
getUsedChoiceNumbersObs st (PersonChoseSomething identch per)
  | not $ Map.member (identch, per) (sch st) = emptyInput {ic = Map.singleton (identch, per) 0}
  | otherwise = emptyInput
getUsedChoiceNumbersObs st (AndObs obs1 obs2) =
  foldl1 combineInputs $ map (getUsedChoiceNumbersObs st) [obs1, obs2]
getUsedChoiceNumbersObs st (OrObs obs1 obs2) =
  foldl1 combineInputs $ map (getUsedChoiceNumbersObs st) [obs1, obs2]
getUsedChoiceNumbersObs st (NotObs obs) = getUsedChoiceNumbersObs st obs
getUsedChoiceNumbersObs st (ValueGE m1 m2) = foldl1 combineInputs $ map (getUsedChoiceNumbersMoney st) [m1, m2]
getUsedChoiceNumbersObs _ _ = emptyInput

-- Obtains all the choices that are potentially checked by a money expression (taken as "0")
getUsedChoiceNumbersMoney :: State -> Money -> Input
getUsedChoiceNumbersMoney st (AddMoney m1 m2) = foldl1 combineInputs $ map (getUsedChoiceNumbersMoney st) [m1, m2]
getUsedChoiceNumbersMoney st (MoneyFromChoice identch per m)
 = foldl1 combineInputs $ [emptyInput {ic = Map.singleton (identch, per) 0}, getUsedChoiceNumbersMoney st m]
getUsedChoiceNumbersMoney st _ = emptyInput

-- Obtains all the choices that are potentially checked by a contract (taken as "0")
getUsedChoiceNumbers :: State -> Contract -> Input
getUsedChoiceNumbers st (CommitCash _ _ m _ _ c1 c2)
 = foldl1 combineInputs $ ((getUsedChoiceNumbersMoney st m):(map (getUsedChoiceNumbers st) [c1, c2]))
getUsedChoiceNumbers st (RedeemCC _ c) = getUsedChoiceNumbers st c
getUsedChoiceNumbers st (Pay _ _ _ m _ c)
 = foldl1 combineInputs $ [getUsedChoiceNumbersMoney st m, getUsedChoiceNumbers st c]
getUsedChoiceNumbers st (Both c1 c2) =
  foldl1 combineInputs $ map (getUsedChoiceNumbers st) [c1, c2]
getUsedChoiceNumbers _ Null = emptyInput
getUsedChoiceNumbers st (Choice obs c1 c2) =
  foldl1 combineInputs (getUsedChoiceNumbersObs st obs : map (getUsedChoiceNumbers st) [c1, c2])
getUsedChoiceNumbers st (When obs _ c1 c2) =
  foldl1 combineInputs (getUsedChoiceNumbersObs st obs : map (getUsedChoiceNumbers st) [c1, c2])

-- Obtains all the valid redeems that can be done because they expired
getPotentialInputsFromState :: OS -> State -> Input
getPotentialInputsFromState os State {sc = commits} =
  emptyInput {rc = Set.fromList [RC ident p val
                                 | (ident, v@(p, NotRedeemed val _)) <- Map.toList commits,
                                   isExpiredNotRedeemed (blockNumber os) v]}

-- Obtains all the interesting inputs that can be done given the situation
-- It takes all choices as "0", independently of what would be useful
getPossibleInputs :: OS -> Input -> Contract -> State -> Input
getPossibleInputs os inp contr stat = foldl1 combineInputs [inputsFromContract, inputsFromState, choices]
  where (statGivenInputs, contractGivenInputs, _) = stepBlock inp stat contr os
        inputsFromContract = getPotentialInputsFromContract os contractGivenInputs statGivenInputs
        inputsFromState = getPotentialInputsFromState os statGivenInputs
        choices = getUsedChoiceNumbers statGivenInputs contractGivenInputs

