module Conversion where

import qualified Semantics as Old
import qualified Minimal as New
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Ord (comparing)
import Data.List (genericTake, genericDrop, genericLength, sortBy, partition)
import Data.Either (isLeft)

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
            , commitPerson :: M.Map Old.IdCommit Old.Person
            , commitIdAc :: M.Map Old.IdCommit (S.Set Old.IdAction)
            , payIdAc :: M.Map Old.IdCommit (S.Set Old.IdAction) }
  deriving (Eq,Ord,Show,Read)

emptyActionData :: ActionData
emptyActionData = ActionData M.empty M.empty M.empty M.empty M.empty

addCommit :: Integer -> Old.IdAction -> Integer -> Old.Person -> ActionData
          -> ActionData
addCommit cid aid cho per ac@(ActionData { idActionChoice = iac 
                                         , commitIdCom = cic
                                         , commitPerson = cp
                                         , commitIdAc = cia}) =
  let result = ac{ idActionChoice = M.insert aid (New.ChoiceId cho per) iac
                 , commitIdCom = M.insertWith (S.union) per (S.singleton cid) cic
                 , commitPerson = M.insert cid per cp
                 , commitIdAc = M.insertWith (S.union) cid (S.singleton aid) cia } in
  case M.lookup cid cp of
    Just y -> if y /= per then error "A commitId can only belong to a single person"
              else result
    Nothing -> result

addPay :: Integer -> Old.IdAction -> Integer -> Old.Person -> ActionData -> ActionData
addPay cid aid cho per ac@(ActionData { idActionChoice = iac
                                      , payIdAc = pia }) =
  ac{ idActionChoice = M.insert aid (New.ChoiceId cho per) iac
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
    Old.Commit ida cid per _ _ _ c1 c2 ->
      let (nluc, cho) = getNewChoiceNum per luc in
      chain (addCommit cid ida cho per ad) nluc c1 c2
    Old.Pay ida cid per _ _ c1 c2 ->
      let (nluc, cho) = getNewChoiceNum per luc in
      chain (addPay cid ida cho per ad) nluc c1 c2
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

data ConvertEnv = ConvertEnv { commits :: M.Map Old.IdCommit Old.Timeout
                             , expiredCommits :: S.Set Old.IdCommit
                             , pays :: S.Set Old.IdAction }
  deriving (Eq,Ord,Show,Read)

emptyConvertEnv :: ConvertEnv
emptyConvertEnv = ConvertEnv M.empty S.empty S.empty

unfoldChoicesAux :: ConvertEnv -> Old.Contract ->
                    Maybe (Old.Observation, (Bool -> Old.Contract))
unfoldChoicesAux env contract =
  case contract of
    Old.Null -> Nothing 
    Old.Commit _ _ _ _ _ _ _ _ -> Nothing
    Old.Pay _ _ _ _ _ _ _ -> Nothing
    Old.Both c1 c2 ->
      case (unfoldChoicesAux env c1, unfoldChoicesAux env c2) of
        (Just (no, f), _) -> Just (no, (\x -> Old.Both (f x) c2))
        (Nothing, Just (no, f)) -> Just (no, (\x -> Old.Both c1 (f x)))
        (Nothing, Nothing) -> Nothing
    Old.Choice o c1 c2 -> Just (o, (\x -> if x then c1 else c2)) 
    Old.When _ _ _ _ -> Nothing 
    Old.While o t c1 c2 -> do (no, f) <- unfoldChoicesAux env c1
                              return (no, (\x -> Old.While o t (f x) c2))
    Old.Scale _ _ _ _ -> error "Scale not implemented" 
    Old.Let _ _ _ -> error "Expand contract before converting" 
    Old.Use _ -> error "Expand contract before converting"

unfoldChoices :: ConvertEnv -> Old.Contract -> Old.Contract
unfoldChoices env c =
  case unfoldChoicesAux env c of
    Nothing -> c
    Just (o, f) -> let nc1 = unfoldChoices env $ f True in
                   let nc2 = unfoldChoices env $ f False in
                   Old.Choice o nc1 nc2 

addValues :: [New.Value] -> New.Value
addValues [] = New.Constant 0 
addValues [x] = x
addValues [x, y] = New.AddValue x y
addValues l = New.AddValue (addValues fp) (addValues sp)
  where fp = genericTake hl l
        sp = genericDrop hl l
        hl = (genericLength l) `div` (2 :: Integer)

andObservations :: [New.Observation] -> New.Observation
andObservations [] = New.TrueObs
andObservations [x] = x
andObservations [x, y] = New.AndObs x y
andObservations l = New.AndObs (andObservations fp) (andObservations sp)
  where fp = genericTake hl l
        sp = genericDrop hl l
        hl = (genericLength l) `div` (2 :: Integer)

remMoney :: ActionData -> ConvertEnv -> Old.IdCommit -> New.Value
remMoney ad ce cid = if isExpiredCommit ce cid
                     then New.Constant 0
                     else New.SubValue (addValues cias) (addValues pias)
  where ciacs = M.findWithDefault S.empty cid $ commitIdAc ad
        piacs = M.findWithDefault S.empty cid $ payIdAc ad
        cias = [ let Just choid = M.lookup c $ idActionChoice ad in
                 New.ChoiceValue choid (New.Constant 0) | c <- (S.toList ciacs) ]
        pias = [ let Just choid = M.lookup p $ idActionChoice ad in
                 New.ChoiceValue choid (New.Constant 0) | p <- (S.toList piacs)
                                                        , p `S.member` vpays ]
        vpays = pays ce

refundEverything :: ActionData -> ConvertEnv ->
                    [(Old.IdCommit, Old.Timeout)] -> New.Contract
refundEverything ad ce list =
  refundEverythingAux ad ce (filter (not . (isExpiredCommit ce) . fst) list)

refundEverythingAux :: ActionData -> ConvertEnv ->
                    [(Old.IdCommit, Old.Timeout)] -> New.Contract
refundEverythingAux _ _ [] = New.Pay [] (Left 1) -- Just pay residue to first participant,
                                                 -- there should be no residue 
refundEverythingAux ad _ [(oid, tim)] = New.When [] tim $ New.Pay [] (Left p)
  where
    Just p = M.lookup oid $ commitPerson ad
refundEverythingAux ad ce ((oid, tim):(t@(_:_))) =
  if s == (New.Constant 0) then refundEverythingAux ad ce t
  else New.When [] tim (New.Pay [(s, p)] $ Right $ refundEverythingAux ad ce t) 
  where 
    Just p = M.lookup oid $ commitPerson ad
    s = remMoney ad ce oid

convertVal :: ActionData -> ConvertEnv -> Old.Value -> New.Value
convertVal ad ce val =
 case val of
   Old.CurrentBlock -> New.CurrentSlot
   Old.Committed idCommit ->
     if (M.member idCommit $ commits ce) && (not $ S.member idCommit $ expiredCommits ce)
     then remMoney ad ce idCommit
     else New.Constant 0
   Old.Constant integer -> New.Constant integer
   Old.NegValue _ -> error "NegValue not implemented" 
   Old.AddValue value1 value2 -> New.AddValue (go value1) (go value2)
   Old.SubValue value1 value2 -> New.SubValue (go value1) (go value2)
   Old.MulValue _ _ -> error "MulValue not implemented" 
   Old.DivValue _ _ _ -> error "DivValue not implemented" 
   Old.ModValue _ _ _ -> error "ModValue not implemented" 
   Old.ValueFromChoice (idChoice, idPer) value ->
     New.ChoiceValue (New.ChoiceId idChoice idPer) (go value)
   Old.ValueFromOracle idOracle value ->
     New.OracleValue (New.OracleId idOracle) (go value)
  where
    go = convertVal ad ce

convertObs :: ActionData -> ConvertEnv -> Old.Observation -> New.Observation
convertObs ad ce obs =
 case obs of
   Old.BelowTimeout timeout -> New.ValueLT (New.CurrentSlot) (New.Constant timeout)
   Old.ChoseThis (idChoice, idPer) cho ->
     New.AndObs (New.ChoseSomething (New.ChoiceId idChoice idPer))
                (New.ValueEQ (New.ChoiceValue (New.ChoiceId idChoice idPer)
                                              (New.Constant 0))
                             (New.Constant cho))
   Old.AndObs obs1 obs2 -> New.AndObs (go obs1) (go obs2)
   Old.OrObs obs1 obs2 -> New.OrObs (go obs1) (go obs2)
   Old.NotObs obs1 -> New.NotObs (go obs1)
   Old.ChoseSomething (idChoice, idPer) -> New.ChoseSomething (New.ChoiceId idChoice idPer)
   Old.ValueGE val1 val2 -> New.ValueGE (goVal val1) (goVal val2)
   Old.ValueGT val1 val2 -> New.ValueGT (goVal val1) (goVal val2)
   Old.ValueLT val1 val2 -> New.ValueLT (goVal val1) (goVal val2)
   Old.ValueLE val1 val2 -> New.ValueLE (goVal val1) (goVal val2)
   Old.ValueEQ val1 val2 -> New.ValueEQ (goVal val1) (goVal val2)
   Old.TrueObs -> New.TrueObs
   Old.FalseObs -> New.FalseObs
  where
    go = convertObs ad ce
    goVal = convertVal ad ce

data QuiescentThread =
  QuiescentThread { convertEnv :: ConvertEnv
                  , guard :: Either New.Timeout New.Observation
                  , continuation :: Old.Contract }

depositCorrect :: ActionData -> ConvertEnv -> Old.Value -> Old.Person
               -> New.Observation
depositCorrect ad ce val per = New.ValueEQ (New.CommittedBy per) amo
  where
    amo = addValues (convertVal ad ce val :
                     (concat [ let Just acIds = M.lookup pc $ commitIdAc ad in
                               [ let Just chId = M.lookup acId $ idActionChoice ad in
                                 New.ChoiceValue chId (New.Constant 0)
                                | acId <- S.toList acIds ]
                              | pc <- S.toList prevComms]))
    Just perComms = M.lookup per $ commitIdCom ad
    prevComms = S.intersection perComms $ M.keysSet $ commits ce

onlyOneCommit :: ActionData -> Old.IdAction -> Old.IdCommit -> New.Value -> New.Observation
onlyOneCommit ad idac idcom val =
  andObservations
    ((New.ValueEQ val $ New.ChoiceValue thisChoice (New.Constant 0)) :
     (New.ChoseSomething thisChoice) :
     othersZero)
  where othersZero = [let Just x = M.lookup comm $ idActionChoice ad in
                      New.NotObs $ New.ValueEQ (New.Constant 0) $
                                               New.ChoiceValue x (New.Constant 1)
                      | comm <- S.toList $ S.delete idac comms]
        Just comms = M.lookup idcom $ commitIdAc ad
        Just thisChoice = M.lookup idac $ idActionChoice ad

signalZero :: ActionData -> Old.IdAction -> New.Observation
signalZero ad idac = New.ValueEQ (New.ChoiceValue x (New.Constant 1)) (New.Constant 0)
  where Just x = M.lookup idac $ idActionChoice ad

enoughMoneyAndClaimedRight :: ActionData -> ConvertEnv -> Old.IdAction -> Old.IdCommit ->
                              New.Value -> New.Observation
enoughMoneyAndClaimedRight ad ce idac idcomm val =
  New.AndObs (New.ValueGE remInComm val)
             (New.AndObs (New.ChoseSomething acChoice)
                         (New.ValueEQ val
                                      (New.ChoiceValue acChoice (New.Constant 0))))
  where remInComm = remMoney ad ce idcomm 
        Just acChoice = M.lookup idac $ idActionChoice ad

notEnoughAndClaimedAll :: ActionData -> ConvertEnv -> Old.IdAction -> Old.IdCommit ->
                          New.Value -> New.Observation
notEnoughAndClaimedAll ad ce idac idcomm val =
  New.AndObs (New.ValueLT remInComm val)
             (New.AndObs (New.ChoseSomething acChoice)
                         (New.ValueEQ val
                                      (New.ChoiceValue acChoice (New.Constant 0))))
  where remInComm = remMoney ad ce idcomm 
        Just acChoice = M.lookup idac $ idActionChoice ad

getQuiescent :: ActionData -> ConvertEnv -> Old.Contract -> [QuiescentThread]
getQuiescent ad ce c =
  case c of
    Old.Null -> []
    Old.Commit iact icom p val t1 t2 c1 c2 ->
      if ((M.lookup icom $ commits ce) /= Nothing)
      then [ QuiescentThread { convertEnv = ce
                             , guard = Left t1
                             , continuation = c2 
                             } ]
      else [ QuiescentThread { convertEnv = ce
                             , guard = Left t1 
                             , continuation = c2 
                             }
           , QuiescentThread { convertEnv = (ce{ commits = M.insert icom t2
                                                                       (commits ce) })
                             , guard = Right $ New.AndObs (depositCorrect ad ce val p)
                                                          (onlyOneCommit ad iact icom
                                                             (convertVal ad ce val)) 
                             , continuation = c1 
                             }
           ]
    Old.Pay iact icom _ val t c1 c2 ->
      let badCommit = [ QuiescentThread { convertEnv = ce
                                        , guard = Left t 
                                        , continuation = c2 
                                        }
                      , QuiescentThread { convertEnv = (ce{ pays = S.insert iact (pays ce) })
                                        , guard = Right (signalZero ad iact)
                                        , continuation = c1
                                        }
                      ] in
      case (M.lookup icom $ commits ce) of
        Just _ ->
          if not $ isExpiredCommit ce icom
          then [ QuiescentThread { convertEnv = ce
                                 , guard = Left t 
                                 , continuation = c2 
                                 }
               , QuiescentThread { convertEnv = (ce{ pays = S.insert iact (pays ce) })
                                 , guard = Right (New.OrObs (enoughMoneyAndClaimedRight
                                                               ad ce iact icom
                                                               (convertVal ad ce val))
                                                            (notEnoughAndClaimedAll
                                                               ad ce iact icom
                                                               (convertVal ad ce val)))
                                 , continuation = c1 
                                 }
               ]
          else badCommit
        Nothing -> badCommit 
    Old.Both c1 c2 -> (go c1 (\x -> Old.Both x c2)) ++ (go c2 (\x -> Old.Both c1 x)) 
    Old.Choice _ _ _ -> error "Internal error: there should not be a Choice here" 
    Old.When obs t c1 c2 ->
       [ QuiescentThread { convertEnv = ce
                         , guard = Left t 
                         , continuation = c2
                         }
       , QuiescentThread { convertEnv = ce
                         , guard = Right $ convertObs ad ce obs
                         , continuation = c1 
                         }
       ]
    Old.While o t c1 c2 ->
       [ QuiescentThread { convertEnv = ce
                         , guard = Left t 
                         , continuation = c2 
                         }
       , QuiescentThread { convertEnv = ce
                         , guard = Right $ New.NotObs $ convertObs ad ce o
                         , continuation = c2 
                         }
       ] ++ (go c1 (\x -> Old.While o t x c2))
    Old.Scale _ _ _ _ -> error "Scale not implemented" 
    Old.Let _ _ _ -> error "Expand contract before converting" 
    Old.Use _ -> error "Expand contract before converting"
  where go c2 f = let xl = getQuiescent ad ce c2 in
                 [x{continuation = f (continuation x)} | x <- xl]

earliestExpiringCommit :: ConvertEnv -> Maybe (Old.IdCommit, Old.Timeout)
earliestExpiringCommit ce =
  case sortedCommits of
    [] -> Nothing
    (h:_) -> Just h
  where sortedCommits = sortBy (comparing snd) $ filterExp $ M.toList $ commits ce
        filterExp = filter (not . (isExpiredCommit ce) . fst)

splitQuiescentThreads :: [QuiescentThread] -> ([QuiescentThread], [QuiescentThread])
splitQuiescentThreads = partition (isLeft . guard)

flattenRest :: ActionData -> [QuiescentThread] -> [New.Case]
flattenRest ad qt = map flattenOne qt
  where flattenOne (QuiescentThread { convertEnv = ce
                                    , guard = g
                                    , continuation = oc }) =
              New.Case (fromRight' g) $ convertAux ad ce oc

addAndFlattenRest :: ActionData -> QuiescentThread -> [QuiescentThread]
                  -> New.Contract
addAndFlattenRest ad tq qt =
  New.When (flattenRest ad qt) (fromLeft' $ guard tq)
           (convertAux ad (convertEnv tq) (continuation tq))

isExpiredCommit :: ConvertEnv -> Old.IdCommit -> Bool
isExpiredCommit ce = (`S.member` (expiredCommits ce))

expireCommit :: Old.IdCommit -> ConvertEnv -> ConvertEnv
expireCommit oid ce = ce{expiredCommits = S.insert oid (expiredCommits ce)}

refundOneAndFlattenRest :: ActionData -> ConvertEnv -> Old.Contract -> Old.IdCommit
                        -> Old.Timeout -> [QuiescentThread] -> New.Contract 
refundOneAndFlattenRest ad ce oc idcomm tim qt =
  New.When (flattenRest ad qt) tim
           (New.Pay [(s, p)] $ Right $ convertAux ad (expireCommit idcomm ce) oc)
  where 
    Just p = M.lookup idcomm $ commitPerson ad
    s = remMoney ad ce idcomm

fromRight' :: Either a b -> b
fromRight' (Right x) = x
fromRight' _ = error "Right expected"

fromLeft' :: Either a b -> a
fromLeft' (Left x) = x
fromLeft' _ = error "Left expected"

flattenQuiescent :: ActionData -> ConvertEnv -> Old.Contract -> [QuiescentThread]
                 -> New.Contract
flattenQuiescent ad ce oc qt =
  case (sortedTimeouts, earliestExpiringCommit ce) of
    ([], Nothing) -> refundEverything ad ce [] 
    ((h:_), Nothing) -> addAndFlattenRest ad h guarded
    ((h:_), Just (idcomm, x)) ->
        if (fromLeft' $ guard h) < x then addAndFlattenRest ad h guarded
        else refundOneAndFlattenRest ad ce oc idcomm x guarded
    ([], Just _) -> refundEverything ad ce $ sortBy (comparing snd) $ M.toList $ commits ce
  where (timeouts, guarded) = splitQuiescentThreads qt
        sortedTimeouts = sortBy (comparing $ fromLeft' . guard) timeouts

skipChoice :: ActionData -> ConvertEnv -> Old.Contract -> New.Contract
skipChoice ad ce (Old.Null) = refundEverything ad ce
                                 (sortBy (comparing snd) $ M.toList $ commits ce)
skipChoice ad ce (Old.Choice o c1 c2) = New.If (convertObs ad ce o) (go c1) (go c2)
  where go = skipChoice ad ce
skipChoice ad ce c = flattenQuiescent ad ce c $ getQuiescent ad ce c

convertAux :: ActionData -> ConvertEnv -> Old.Contract -> New.Contract
convertAux ad ce c = skipChoice ad ce (unfoldChoices ce c)

convert :: Old.Contract -> (New.Contract, ActionData)
convert contract = (convertAux renamings emptyConvertEnv contract, renamings)
  where (renamings, _) = idActionToChoice emptyActionData maxChoices contract
        maxChoices = maxUsedChoices contract


