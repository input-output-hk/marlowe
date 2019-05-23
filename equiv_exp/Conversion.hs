module Conversion where

import qualified Semantics as Old
import qualified Minimal as New
import qualified Data.Map.Strict as M
import qualified Data.Set as S

type LastUsedChoice = M.Map Old.Person New.NumChoice

maxUsedChoicesVal :: Old.Value -> LastUsedChoice
maxUsedChoicesVal value =
  case value of
    Old.CurrentBlock -> M.empty
    Old.Committed _ -> M.empty
    Old.Constant _ -> M.empty 
    Old.NegValue v -> goV v
    Old.AddValue v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.SubValue v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.MulValue v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.DivValue v1 v2 v3 -> joinRes $ map goV $ [v1, v2, v3]
    Old.ModValue v1 v2 v3 -> joinRes $ map goV $ [v1, v2, v3]
    Old.ValueFromChoice (nc, per) v -> joinRes $ [M.singleton per nc, goV v]
    Old.ValueFromOracle _ v -> goV v 
  where goV = maxUsedChoicesVal
        joinRes = M.unionsWith (max)

maxUsedChoicesObs :: Old.Observation -> LastUsedChoice
maxUsedChoicesObs observation =
  case observation of
    Old.BelowTimeout _ -> M.empty
    Old.AndObs o1 o2 -> joinRes $ map goO $ [o1, o2]
    Old.OrObs o1 o2 -> joinRes $ map goO $ [o1, o2]
    Old.NotObs o -> goO o
    Old.ChoseThis (nc, per) _ -> M.singleton per nc
    Old.ChoseSomething (nc, per) -> M.singleton per nc
    Old.ValueGE v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.ValueGT v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.ValueLT v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.ValueLE v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.ValueEQ v1 v2 -> joinRes $ map goV $ [v1, v2]
    Old.TrueObs -> M.empty
    Old.FalseObs -> M.empty
  where goO = maxUsedChoicesObs
        goV = maxUsedChoicesVal
        joinRes = M.unionsWith (max)
 
maxUsedChoices :: Old.Contract -> LastUsedChoice
maxUsedChoices contract =
  case contract of
    Old.Null -> M.empty
    Old.Commit _ _ _ v _ _ c1 c2 -> joinRes $ (goV v):(map goC [c1, c2])
    Old.Pay _ _ _ v _ c1 c2 -> joinRes $ (goV v):(map goC [c1, c2])
    Old.Both c1 c2 -> joinRes $ map goC $ [c1, c2]
    Old.Choice o c1 c2 -> joinRes $ (goO o):(map goC [c1, c2])
    Old.When o _ c1 c2 -> joinRes $ (goO o):(map goC [c1, c2])
    Old.While o _ c1 c2 -> joinRes $ (goO o):(map goC [c1, c2])
    Old.Scale v1 v2 v3 c -> joinRes $ (goC c):(map goV [v1, v2, v3])
    Old.Let _ c1 c2 -> joinRes $ map goC $ [c1, c2]
    Old.Use _ -> M.empty
  where goC = maxUsedChoices
        goO = maxUsedChoicesObs
        goV = maxUsedChoicesVal
        joinRes = M.unionsWith (max)

data ActionData =
 ActionData { idActionChoice :: M.Map Old.IdAction New.ChoiceId
            , commitIdCom :: M.Map Old.Person (S.Set Old.IdCommit)
            , commitIdAc :: M.Map Old.IdCommit (S.Set Old.IdAction)
            , payIdAc :: M.Map Old.IdCommit (S.Set Old.IdAction) }
  deriving (Eq,Ord,Show,Read)

emptyActionData :: ActionData
emptyActionData = ActionData M.empty M.empty M.empty M.empty

addCommit :: Integer -> Old.IdAction -> Old.Person -> ActionData -> ActionData
addCommit cid aid per ac@(ActionData { idActionChoice = iac 
                                     , commitIdCom = cic
                                     , commitIdAc = cia}) =
  ac{ idActionChoice = M.insert aid (New.ChoiceId cid per) iac
    , commitIdCom = M.insertWith (S.union) per (S.singleton cid) cic
    , commitIdAc = M.insertWith (S.union) cid (S.singleton aid) cia }

addPay :: Integer -> Old.IdAction -> Old.Person -> ActionData -> ActionData
addPay cid aid per ac@(ActionData { idActionChoice = iac
                                  , payIdAc = pia }) =
  ac{ idActionChoice = M.insert aid (New.ChoiceId cid per) iac
    , payIdAc = M.insertWith (S.union) cid (S.singleton aid) pia }

getNewChoiceNum :: Old.Person -> LastUsedChoice -> (LastUsedChoice, Old.Person)
getNewChoiceNum per luc =
  case M.lookup per luc of
    Just x -> let nx = x + 1 in (M.insert per nx luc, nx)
    Nothing -> (M.insert per 1 luc, 1)

idActionToChoice :: ActionData -> LastUsedChoice -> Old.Contract
                   -> (ActionData, LastUsedChoice)
idActionToChoice ad luc contract =
  case contract of
    Old.Null -> (ad, luc)
    Old.Commit ida _ per _ _ _ c1 c2 ->
      let (nluc, cid) = getNewChoiceNum per luc in
      chain (addCommit cid ida per ad) nluc c1 c2
    Old.Pay ida _ per _ _ c1 c2 ->
      let (nluc, cid) = getNewChoiceNum per luc in
      chain (addPay cid ida per ad) nluc c1 c2
    Old.Both c1 c2 -> chain2 c1 c2
    Old.Choice _ c1 c2 -> chain2 c1 c2
    Old.When _ _ c1 c2 -> chain2 c1 c2
    Old.While _ _ c1 c2 -> chain2 c1 c2
    Old.Scale _ _ _ c -> idActionToChoice ad luc c
    Old.Let _ c1 c2 -> chain2 c1 c2
    Old.Use _ -> (ad, luc)
  where chain2 = chain ad luc
        chain oad oluc c1 c2 = let (adt, luct) = idActionToChoice oad oluc c1 in
                                   idActionToChoice adt luct c2

data ConvertEnv = ConvertEnv {  }
  deriving (Eq,Ord,Show,Read)

emptyConvertEnv :: ConvertEnv
emptyConvertEnv = ConvertEnv

convertAux :: ActionData -> ConvertEnv -> Old.Contract -> New.Contract
convertAux ad ce c = convertAux ad ce c


convert :: Old.Contract -> (New.Contract, ActionData)
convert contract = (convertAux renamings emptyConvertEnv contract, renamings)
  where (renamings, _) = idActionToChoice emptyActionData maxChoices contract
        maxChoices = maxUsedChoices contract


