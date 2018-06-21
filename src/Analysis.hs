
module Analysis where

import Semantics
import LogicSolve
import Data.List (foldl', sort, sortBy)
import Data.Maybe (fromMaybe, isJust)
import Control.Monad (replicateM)
import qualified Data.Map as Map
import qualified Data.Set as Set

{---------------------------------
 - Concrete trace representation -
 ---------------------------------}

type ConcreteTrace = [Input]

-- Increases the block in the observables by one
incBlock :: OS -> OS
incBlock os@(OS {blockNumber = bn}) = os {blockNumber = bn + 1}

-- Executes a concrete trace and outputs the list of actions produced
-- every entry in the trace represents the inputs for a different block
executeConcreteTrace :: Contract -> ConcreteTrace -> AS
executeConcreteTrace contract concreteTrace = reverse $ finalAcc
  where
    iniAcc = (emptyState, contract, emptyOS, [])
    stepFunc (sta, contr, os, accs) inps = let (nsta, ncon, naccs) = stepBlock inps sta contr os in
                                           (nsta, ncon, incBlock os, (reverse naccs) ++ accs)
    (_, _, _, finalAcc) = foldl' stepFunc iniAcc concreteTrace

displayTrace :: Maybe [Input] -> IO ()
displayTrace Nothing = return ()
displayTrace (Just x) = do putStrLn "******"
                           mapM_ (putStrLn . show) x

showConcreteTraces :: Contract -> IO ()
showConcreteTraces c =
  do putStrLn "Possible concrete traces:"
     mapM_ (displayTrace) ct
  where st = analyseContract c
        ct = map symbolicToConcreteTrace st



{---------------------------------
 - Abstract trace representation -
 ---------------------------------}

type SLogic = Logic AnalysisVariable
type VarExpr = [EquationTerm AnalysisVariable] 

data InputIdentifier = CommitID IdentCC
                     | RedeemID IdentCC
                     | PaymentID IdentPay Person
                     | ChoiceID IdentChoice Person
               deriving (Eq,Ord,Show,Read)

data InputDetInfo = CommitDI IdentCC Person Timeout
                  | RedeemDI IdentCC Person
                  | PaymentDI IdentPay Person
                  | ChoiceDI IdentChoice Person
               deriving (Eq,Ord,Show,Read)

getIdentifier :: InputDetInfo -> InputIdentifier
getIdentifier (CommitDI ide _ _) = CommitID ide
getIdentifier (RedeemDI ide _) = RedeemID ide
getIdentifier (PaymentDI ide per) = PaymentID ide per
getIdentifier (ChoiceDI ide per) = ChoiceID ide per

data AnalysisVariable = CurrentBlock {- Global (last block considered) -}
                      | TempVar Integer {- Temporal variable for internal constraints -}
           -- Generic vars
                      | InputIssued InputIdentifier {- Positive (or zero): issued; negative: not issued -}
                      | InputIssueBlock InputIdentifier {- Block number when issued (always positive or zero) -}
           -- Commit specific
                      | CommitAmmount IdentCC {- Money committed -}
           -- Redeem specific
                      | RedeemAmmount IdentCC {- Money redeemed -}
           -- Payment specific
                      | PaymentAmmount IdentPay Person {- Money claimed -}
           -- Choice specific
                      | ChoiceValue IdentChoice Person {- Concrete choice made -}
               deriving (Eq,Ord,Show,Read)

inputIdFromVariable :: AnalysisVariable -> Maybe InputIdentifier
inputIdFromVariable CurrentBlock = Nothing
inputIdFromVariable (TempVar _) = Nothing
inputIdFromVariable (InputIssued ide) = Just $ ide 
inputIdFromVariable (InputIssueBlock ide) = Just $ ide 
inputIdFromVariable (CommitAmmount ide) = Just $ CommitID ide 
inputIdFromVariable (RedeemAmmount ide) = Just $ RedeemID ide 
inputIdFromVariable (PaymentAmmount ide per) = Just $ PaymentID ide per
inputIdFromVariable (ChoiceValue ide per) = Just $ ChoiceID ide per

type SCCStatus = (Person, SCCRedeemStatus)
data SCCRedeemStatus = SNotRedeemed VarExpr Timeout | SManuallyRedeemed
               deriving (Eq,Ord,Show,Read)
data SState = SState {ssc :: Map.Map IdentCC SCCStatus,
                      ssch :: Map.Map (IdentChoice, Person) VarExpr}
               deriving (Eq,Ord,Show,Read)

emptySymbolicState :: SState
emptySymbolicState = SState { ssc = Map.empty,
                              ssch = Map.empty } 

type Explanation = String

data SymbolicTrace = SymbolicTrace { lastIndex :: Integer,
                                     constraints :: SLogic,
                                     inputs :: Map.Map InputIdentifier InputDetInfo,
                                     currentBlock :: VarExpr,
                                     symState :: SState,
                                     explanation :: [Explanation] }
               deriving (Eq,Ord,Show,Read)

emptySymbolicTrace :: SymbolicTrace
emptySymbolicTrace = SymbolicTrace { lastIndex = nind,
                                     constraints = (Eq $ LE (constant 0) tvar),
                                     inputs = Map.empty,
                                     currentBlock = tvar,
                                     symState = emptySymbolicState,
                                     explanation = []}
  where (nind, tvar) = generateAV 0

{---------------------------------------
 - Abstract to concrete transformation -
 ---------------------------------------}

data InputConcreteData = CommitCD IdentCC Person Timeout (Maybe Cash)
                       | RedeemCD IdentCC Person (Maybe Cash)
                       | PaymentCD IdentPay Person (Maybe Cash)
                       | ChoiceCD IdentChoice Person (Maybe ConcreteChoice)
               deriving (Eq,Ord,Show,Read)

type InputConcreteDataGen = (Maybe Integer, InputConcreteData)

-- Convert InputDetInfo to an incomplete InputConcreteData (gaps are Nothings)
convertToEmptyConcreteData :: InputDetInfo -> InputConcreteData
convertToEmptyConcreteData (CommitDI ide per tim) = CommitCD ide per tim Nothing
convertToEmptyConcreteData (RedeemDI ide per) = RedeemCD ide per Nothing
convertToEmptyConcreteData (PaymentDI ide per) = PaymentCD ide per Nothing 
convertToEmptyConcreteData (ChoiceDI ide per) = ChoiceCD ide per Nothing 

-- Adds a generic concreteDataInput to an Input set of Marlowe (fill Nothings with zero)
addConcreteData :: InputConcreteData -> Input -> Input
addConcreteData (CommitCD ide per tim mCash) (inp@(Input { cc = ccset })) =
  inp { cc = Set.insert (CC ide per (fromMaybe 0 mCash) tim) ccset }
addConcreteData (RedeemCD ide per mCash) (inp@(Input { rc = rcset })) =
  inp { rc = Set.insert (RC ide per (fromMaybe 0 mCash)) rcset }
addConcreteData (PaymentCD ide per mCash) (inp@(Input { rp = rpmap })) =
  inp { rp = Map.insert (ide, per) (fromMaybe 0 mCash) rpmap }
addConcreteData (ChoiceCD ide per mChoice) (inp@(Input { ic = icmap })) =
  inp { ic = Map.insert (ide, per) (fromMaybe 0 mChoice) icmap }

-- Groups information about inputs together into a list sorted by block number of issue of the input
compileListAux :: SymbolicTrace -> Map.Map InputIdentifier InputConcreteDataGen
                  -> (AnalysisVariable, Integer) -> Map.Map InputIdentifier InputConcreteDataGen
compileListAux _ compMap (CurrentBlock, _) = compMap
compileListAux _ compMap (TempVar _, _) = compMap
compileListAux (SymbolicTrace {inputs = inps}) compMap (InputIssued ide, val)
  | val < 0 = compMap
  | otherwise = case Map.lookup ide inps of
                  Just x -> Map.insert ide (Nothing, (convertToEmptyConcreteData x)) compMap
                  Nothing -> case ide of
                                -- We make an exception for ChoiceID since there
                                -- is not a clear time to issue them
                                ChoiceID cid cper -> Map.insert ide (Nothing, (convertToEmptyConcreteData
                                                                                (ChoiceDI cid cper))) compMap
                                _ -> error "Inconsistent symbolic trace in compileList"
compileListAux _ compMap (InputIssueBlock ide, val)
             -- We assume negative block is not possible (start at 0)
  | val < 0 = error "Negative block number in compileList" 
  | otherwise = case Map.lookup ide compMap of
                  Just (Nothing, cdat) -> Map.insert ide (Just val, cdat) compMap
                  _ -> error "Inconsistent symbolic trace in compileList"
compileListAux _ compMap (CommitAmmount ide, val)
             -- We assume is not possible to commit a negative ammount of money
  | val < 0 = error "Negative money committed in compileList" 
  | otherwise = case Map.lookup completeId compMap of
                  Just (tim, CommitCD cide per timout _) ->
                          Map.insert completeId (tim, CommitCD cide per timout $ Just val) compMap
                  _ -> Map.delete completeId compMap
  where completeId = CommitID ide
compileListAux _ compMap (RedeemAmmount ide, val)
             -- We assume is not possible to redeem a negative ammount of money
  | val < 0 = error "Negative money redeemed in compileList" 
  | otherwise = case Map.lookup completeId compMap of
                  Just (tim, RedeemCD cide per _) ->
                          Map.insert completeId (tim, RedeemCD cide per $ Just val) compMap
                  _ -> Map.delete completeId compMap
  where completeId = RedeemID ide
compileListAux _ compMap (PaymentAmmount ide per, val)
             -- We assume is not possible to pay a negative ammount of money
  | val < 0 = error "Negative money payed in compileList" 
  | otherwise = case Map.lookup completeId compMap of
                  Just (tim, PaymentCD cide cper _) ->
                          Map.insert completeId (tim, PaymentCD cide cper $ Just val) compMap
                  _ -> Map.delete completeId compMap
  where completeId = PaymentID ide per
compileListAux _ compMap (ChoiceValue ide per, val) =
  case Map.lookup completeId compMap of
     Just (tim, ChoiceCD cide cper _) -> Map.insert completeId (tim, ChoiceCD cide cper $ Just val) compMap
     _ -> Map.delete completeId compMap
  where completeId = ChoiceID ide per

compileList :: SymbolicTrace -> [(AnalysisVariable, Integer)] -> [(Integer, InputConcreteData)]
compileList st list = sort [(fromMaybe 0 emi, cdat) | (_, (emi, cdat)) <- Map.toList compiledMap]
  where compiledMap = foldl' (compileListAux st) (Map.empty) list

-- Transform a symbolic trace together with its solution into a concrete trace
symbolicToConcreteTraceAux :: Input -> [(Integer, InputConcreteData)] -> Integer -> Integer -> ConcreteTrace
symbolicToConcreteTraceAux inp [] currBlk lastBlk
  | currBlk <= lastBlk = (inp:(symbolicToConcreteTraceAux emptyInput [] (currBlk + 1) lastBlk))
  | otherwise = []
symbolicToConcreteTraceAux inp l@((emi, cinp):t) currBlk lastBlk
  | emi == currBlk = symbolicToConcreteTraceAux (addConcreteData cinp inp) t currBlk lastBlk
  | emi > currBlk = (inp:(symbolicToConcreteTraceAux emptyInput l (currBlk + 1) lastBlk))
  | otherwise = error "Symbolic trace out of order in symbolicToConcreteTrace"

-- Transform a symbolic trace into a concrete one if possible
symbolicToConcreteTrace :: SymbolicTrace -> Maybe ConcreteTrace
symbolicToConcreteTrace st@(SymbolicTrace {constraints = constr}) =
  case solveLogic constr of
    Nothing -> Nothing
    Just x -> let (list, blk) = (case sort x of
                                  ((CurrentBlock, iblk):ilist) -> (ilist, iblk)
                                  ilist -> (ilist, 0)) in
              Just $ symbolicToConcreteTraceAux emptyInput (compileList st list) 0 blk

{----------------------------
 - Symbolic execution monad -
 ----------------------------}

newtype Worlds s a = Worlds { runWorld :: s -> [(a, s)] }

instance Monad (Worlds s) where
   Worlds { runWorld = f } >>= k =
       let stepWorld s0 = concat [let f2 = runWorld (k x) in f2 s1
                                  | (x, s1) <- f s0] in
       Worlds { runWorld = stepWorld }

instance Applicative (Worlds s) where
  pure a = Worlds { runWorld = (\s -> [(a, s)]) }
  (Worlds { runWorld = mfab }) <*> (Worlds { runWorld = mfa }) =
       Worlds { runWorld = (\s -> concat [[(x y, s2) | (y, s2) <- mfa s1] | (x, s1) <- mfab s]) }

instance Functor (Worlds s) where
  fmap f2 (Worlds { runWorld = f }) =
       Worlds { runWorld = (\s -> [(f2 x, s1) | (x, s1) <- f s]) }

type SE a = Worlds SymbolicTrace a

extractSymbolicTraces :: SymbolicTrace -> SE a -> [(a, SymbolicTrace)]
extractSymbolicTraces st (Worlds {runWorld = f}) = f st

makeBranchingGetter :: (SymbolicTrace -> [a]) -> SE a
makeBranchingGetter f = Worlds { runWorld = \y -> [(x, y) | x <- f y] }

makeGetter :: (SymbolicTrace -> a) -> SE a
makeGetter f = makeBranchingGetter (\x -> [f x])

destroyBranch :: SE a
destroyBranch = Worlds { runWorld = \_ -> [] }

makeBranchingSetter :: (SymbolicTrace -> [SymbolicTrace]) -> SE ()
makeBranchingSetter f = Worlds { runWorld = \y -> [((), x) | x <- f y] }

makeSetter :: (SymbolicTrace -> SymbolicTrace) -> SE ()
makeSetter f = makeBranchingSetter (\x -> [f x]) 

getBlockNum :: SE VarExpr 
getBlockNum = makeGetter currentBlock

setBlockNum :: VarExpr -> SE ()
setBlockNum bn = makeSetter setter
  where setter sy = sy {currentBlock = bn}

getLastIndex :: SE Integer
getLastIndex = makeGetter lastIndex

setLastIndex :: Integer -> SE ()
setLastIndex nidx = makeSetter setter
  where setter sy = sy {lastIndex = nidx}

newVar :: SE VarExpr
newVar =
  do li <- getLastIndex
     (let (nli, var) = generateAV li in
      do setLastIndex nli
         return var)

allowWait :: SE ()
allowWait =
  do nbn <- newVar
     bn <- getBlockNum
     setBlockNum nbn
     addConstraint (Eq $ LE bn nbn)

getInput :: InputIdentifier -> SE (Maybe InputDetInfo)
getInput ide = makeGetter ((Map.lookup ide) . inputs)

setInput :: InputIdentifier -> InputDetInfo -> SE ()
setInput ide val = makeSetter setter
  where setter sy@(SymbolicTrace {inputs = inp}) = sy {inputs = (Map.insert ide val inp)}

branch :: SE a -> SE a -> SE a
branch (Worlds {runWorld = fa}) (Worlds {runWorld = fb}) = Worlds { runWorld = \y -> fa y ++ fb y }

addConstraintAux :: SLogic -> (SymbolicTrace -> SymbolicTrace)
addConstraintAux logi (st@(SymbolicTrace {constraints = ologi})) =
  st {constraints = And [logi, ologi]}

addConstraint :: SLogic -> SE ()
addConstraint x = makeSetter (addConstraintAux x)

addExplanationAux :: Explanation -> (SymbolicTrace -> SymbolicTrace)
addExplanationAux expl (x@(SymbolicTrace {explanation = ta})) =
  x {explanation = expl:ta}

addExplanation :: Explanation -> SE ()
addExplanation x = makeSetter (addExplanationAux x)

ifThenElseSymb :: SLogic -> SE a -> SE a -> SE a 
ifThenElseSymb logi td ed = branch (do { addConstraint (logi) ; td })
                                   (do { addConstraint (Not logi) ; ed })

setAnalysisVar :: AnalysisVariable -> VarExpr -> SE ()
setAnalysisVar av ve = addConstraint (generateEq [Var $ av] ve) 

setIssued :: InputIdentifier -> SE ()
setIssued ide = addConstraint (Eq $ LE [Const 0] [Var $ InputIssued ide])

setIssueBlock :: InputIdentifier -> SE ()
setIssueBlock ide =
  do veBlock <- getBlockNum
     setAnalysisVar (InputIssueBlock ide) veBlock

wasIssuedBeforeOrAt :: InputIdentifier -> VarExpr -> SLogic
wasIssuedBeforeOrAt ide ve = And [ Eq $ LE [Const 0] [Var $ InputIssued ide]
                                 , Eq $ LE [Var $ InputIssueBlock ide] ve ]

addClaim :: IdentPay -> Person -> VarExpr -> SE ()
addClaim ide per veMon =
  do currClaim <- getInput gIde 
     case currClaim of
       Nothing -> do setInput gIde (PaymentDI ide per)
                     setIssued gIde
                     setIssueBlock gIde
                     setAnalysisVar (PaymentAmmount ide per) veMon 
       Just _ -> destroyBranch
  where gIde = PaymentID ide per

addCommit :: IdentCC -> Person -> VarExpr -> Timeout -> SE ()
addCommit ide per veMon tim =
  do currCommit <- getInput gIde
     case currCommit of
       Nothing -> do setInput gIde (CommitDI ide per tim)
                     setIssued gIde
                     setIssueBlock gIde
                     setAnalysisVar (CommitAmmount ide) veMon
       Just _ -> destroyBranch
  where gIde = CommitID ide

addRedeem :: IdentCC -> Person -> VarExpr -> SE ()
addRedeem ide per veMon =
  do currRedeem <- getInput gIde
     case currRedeem of
       Nothing -> do setInput gIde (RedeemDI ide per)
                     setIssued gIde
                     setIssueBlock gIde
                     setAnalysisVar (RedeemAmmount ide) veMon
       Just _ -> destroyBranch
  where gIde = RedeemID ide

addCommitToState :: IdentCC -> (Person, SCCRedeemStatus) -> SE () 
addCommitToState ide val =
  do ssta <- getSymState
     (let sscm = ssc ssta in
      case Map.lookup ide sscm of
        Nothing -> setSymState $ ssta { ssc = Map.insert ide val sscm }
        Just _ -> destroyBranch)

getSymState :: SE SState
getSymState = makeGetter symState

setSymState :: SState -> SE ()
setSymState sstate = makeSetter (\str -> str {symState = sstate})

sortSymByExpiration :: [(IdentCC, SCCStatus)] -> [(IdentCC, SCCStatus)]
sortSymByExpiration = sortBy lowerExpirationDateSym

lowerExpirationDateSym :: (IdentCC, SCCStatus) -> (IdentCC, SCCStatus) -> Ordering
lowerExpirationDateSym (IdentCC id1, (_, SNotRedeemed _ e)) (IdentCC id2, (_, SNotRedeemed _ e2)) =
  case compare e e2 of
    EQ -> compare id1 id2
    o -> o
lowerExpirationDateSym (_, (_, SNotRedeemed _ _)) _ = LT
lowerExpirationDateSym _ (_, (_, SNotRedeemed _ _)) = GT
lowerExpirationDateSym _ _ = EQ

-- Change expired values to zero
filterExpired :: [(IdentCC, SCCStatus)] -> SE [(IdentCC, SCCStatus)]
filterExpired ((i, (p, SNotRedeemed v e)):t) =
  do nvv <- nv
     rest <- filterExpired t
     return ((i, (p, SNotRedeemed nvv e)):rest)
  where
   nv = -- If expired
        symIfExpiredTV (constant e)
          -- Then
          [Const 0]
          -- Else
          v
filterExpired _ = return []

getSortedUnexpiredCommitsBy :: Person -> SE [(IdentCC, SCCStatus)]
getSortedUnexpiredCommitsBy per =
  do sstat <- getSymState
     filterExpired $ sortSymByExpiration $ filter ((== per) . fst . snd) $ Map.toList $ ssc $ sstat

getCommVals :: [(IdentCC, SCCStatus)] -> [VarExpr]
getCommVals l = [v | (_, (_, SNotRedeemed v _)) <- l]

-- Discount the provided (negative) ammount from the commit
discountCommValue :: IdentCC -> VarExpr -> SE ()
discountCommValue ide val =
  do ssta <- getSymState
     (let sscm = ssc ssta in
      case Map.lookup ide sscm of
        Just (p, SNotRedeemed v e) -> setSymState $ ssta {ssc = Map.insert ide (p, SNotRedeemed (v ++ val) e) sscm}
        _ -> error "Commit is not available in updateCommValue")

 
invertVarExpr :: VarExpr -> [EquationTerm AnalysisVariable]
invertVarExpr [] = []
invertVarExpr ((Const x):t) = (Const (-x)):(invertVarExpr t)
invertVarExpr ((NegVar x):t) = (Var x):(invertVarExpr t)
invertVarExpr ((Var x):t) = (NegVar x):(invertVarExpr t)

discountMonFrom :: VarExpr -> [(IdentCC, SCCStatus)] -> SE ()
discountMonFrom _ [] = return () 
discountMonFrom _ ((_, (_, SManuallyRedeemed)):_) = error "Redeemed commit in discountMonFrom"
discountMonFrom v1 ((i, (_, SNotRedeemed v2 _)):t) = 
  do dv <- dvv
     let idv = invertVarExpr dv in
       (do discountCommValue i dv
           discountMonFrom (v1 ++ dv) t)
  where dvv = -- If there is enough money in this commit
              ifThenElseSymTV (Eq $ LE v1 v2)
                -- Then just discount the remaining v1
                v1
                -- Else discount the remaining v2
                v2
                              
{----------------------
 - Symbolic execution -
 ----------------------}

allowsWait :: Contract -> Bool
allowsWait Null = True
allowsWait (CommitCash _ _ _ _ _ _ _) = True
allowsWait (RedeemCC _ _) = True
allowsWait (Pay _ _ _ _ _ _) = True
allowsWait (Both x y) = (allowsWait x) && (allowsWait y)
allowsWait (Choice _ _ _) = False
allowsWait (When _ _ _ _) = False

analyseMoney :: Money -> SE VarExpr
analyseMoney (AvailableMoney ide) =
  do ssta <- getSymState
     case Map.lookup ide $ ssc ssta of
       Just (_, SNotRedeemed v e) -> symIfExpiredTV (constant e)
                                       [Const 0] -- If expired return 0
                                       v -- If not expired return the value
       _ -> return [Const 0] -- If not found return 0
analyseMoney (AddMoney x y) =
  do vx <- analyseMoney x
     vy <- analyseMoney y
     return (vx ++ vy)
analyseMoney (ConstMoney x) =
  return [Const x]
analyseMoney (MoneyFromChoice ide per m) =
  do bn <- getBlockNum
     vm <- analyseMoney m
     ifThenElseSymTV (gide `wasIssuedBeforeOrAt` bn)
       [Var $ ChoiceValue ide per] -- If choice issued before or in currentBlock return choice
       vm -- Else return default
  where gide = ChoiceID ide per

-- The returned integer represents True if ">= 0" or False if "<= -1"
analyseObservation :: Observation -> SE VarExpr
analyseObservation (BelowTimeout x) =
  -- If not below the timeout
  do symIfExpiredTV (constant x)
       -- Then return False
       [Const (-1)]
       -- Else return True
       [Const 0]
analyseObservation (AndObs obs1 obs2) =
  do vobs1 <- analyseObservation obs1
     vobs2 <- analyseObservation obs2 
     -- If both observations are >= 0 
     ifThenElseSymTV (And [Eq $ LE [Const 0] vobs1, Eq $ LE [Const 0] vobs2])
     -- Then
       [Const 0]
     -- Else
       [Const (-1)]
analyseObservation (OrObs obs1 obs2) =
  do vobs1 <- analyseObservation obs1
     vobs2 <- analyseObservation obs2 
     -- If one observation is >= 0 
     ifThenElseSymTV (Or [Eq $ LE [Const 0] vobs1, Eq $ LE [Const 0] vobs2])
     -- Then
       [Const 0]
     -- Else
       [Const (-1)]
analyseObservation (NotObs obs) =
  do vobs <- analyseObservation obs
     -- If observation is >= 0 
     ifThenElseSymTV (Eq $ LE [Const 0] vobs)
     -- Then
       [Const (-1)]
     -- Else
       [Const 0]
analyseObservation (PersonChoseThis ide per cchoice) =
  do bn <- getBlockNum
     ifThenElseSymTV (And [gide `wasIssuedBeforeOrAt` bn,
                          generateEq [Const cchoice] [Var $ ChoiceValue ide per]])
       [Const 0] -- If choice issued before or in currentBlock and equals cchoice return True
       [Const (-1)] -- Else return False
  where gide = ChoiceID ide per
analyseObservation (PersonChoseSomething ide per) =
  do bn <- getBlockNum
     ifThenElseSymTV (gide `wasIssuedBeforeOrAt` bn)
       [Const 0] -- If choice issued before or in currentBlock return True
       [Const (-1)] -- Else return False
  where gide = ChoiceID ide per
analyseObservation (ValueGE m1 m2) =
  do vmon1 <- analyseMoney m1
     vmon2 <- analyseMoney m2
     -- If m1 >= m2
     ifThenElseSymTV (Eq $ LE vmon2 vmon1)
     -- Then
       [Const 0]
     -- Else
       [Const 1]
analyseObservation TrueObs =
  return [Const 0]
analyseObservation FalseObs =
  return [Const (-1)]

analyseContractStep :: Contract -> SE Contract
analyseContractStep Null = destroyBranch 
analyseContractStep (Pay idpay from to val expi con) =
  do allowWait
     -- If expired
     symIfExpired (constant expi)
        -- Then
        (do addExplanation ("Wait for payment \"" ++ show idpay ++ "\" to expire.")
            return con)
        -- Else
        (do veMon <- analyseMoney val
            addClaim idpay to veMon
            remMon <- getSortedUnexpiredCommitsBy from
            -- If enough money
            ifThenElseSymb (Eq $ LE veMon $ concat $ getCommVals remMon)
                -- Then
                (do addExplanation ("Claim payment \"" ++ show idpay ++ "\", there is enough money.")
                    discountMonFrom veMon remMon
                    return con)
                -- Else
                (do addExplanation ("Claim payment \"" ++ show idpay ++ "\", but there is not enough money.")
                    return con))
analyseContractStep (CommitCash ident person val start_timeout end_timeout con1 con2) =
  do allowWait
     -- If expired
     symIfExpired (constant $ min start_timeout end_timeout)
       -- Then
       (do addExplanation ("Wait for commit \"" ++ show ident ++ "\" to expire.")
           addCommitToState ident (person, SManuallyRedeemed)
           return con2)
       -- Else
       (do addExplanation ("Satisfy the commit \"" ++ show ident ++ "\".")
           veMon <- analyseMoney val
           addCommit ident person veMon end_timeout
           addCommitToState ident (person, SNotRedeemed veMon end_timeout)
           return con1)
analyseContractStep (RedeemCC ident con) =
  do allowWait
     st <- getSymState
     (let sccs = ssc st in
      case Map.lookup ident sccs of
        Just (person, SNotRedeemed val _) ->
          (do addExplanation ("Redeem the commit \"" ++ show ident ++ "\".")
              setSymState $ st {ssc = Map.insert ident (person, SManuallyRedeemed) sccs}
              addRedeem ident person val
              return con)
        Just (_, SManuallyRedeemed) -> (do addExplanation ("The commit \"" ++ show ident ++ "\" was already redeemed.")
                                           return con)
        Nothing -> destroyBranch)
analyseContractStep b@(Both con1 con2) =
  -- Note: we are treating this as if you had the choice to not execute one of the
  -- branches, this is not accurate, but it just adds some fake possibilities
  do if (allowsWait b) then allowWait else (return ())
     branch (do nc1 <- analyseContractStep con1
                branch (do nc2 <- analyseContractStep con2
                           return (Both nc1 nc2))
                       (do if (allowsWait con2) then (return ()) else destroyBranch
                           return (Both nc1 con2)))
            (do if (allowsWait con1) then (return ()) else destroyBranch
                nc2 <- analyseContractStep con2
                return (Both con1 nc2))
analyseContractStep (Choice obs conT conF) =
  do vobs <- analyseObservation obs
     -- If obs is True
     ifThenElseSymb (Eq $ LE [Const 0] vobs)
       -- Then
       (do addExplanation ("Make sure that the following observation is satisfied: " ++ show obs)
           return conT)
       -- Else
       (do addExplanation ("Make sure that the following observation is not satisfied: " ++ show obs)
           return conF)
analyseContractStep (When obs expi con con2) =
     -- If When is expired
  do allowWait
     symIfExpired [Const expi]
       -- Then
       (do addExplanation ("Wait for the When to expire without satisfying the following observation: " ++ show obs)
           return con2)
       -- Else
       (do addExplanation ("Make sure that the following observation in the When is satisfied: " ++ show obs)
           vobs <- analyseObservation obs -- Ensure obs is true
           -- Note: we are not filtering cases when blockNumber is not minimal
           -- this may result in extra case, but filtering them would add a lot
           -- of complexity so it is probably not a good idea
           addConstraint (Eq $ LE [Const 0] vobs)
           return con)

analyseContractAux :: [(Contract, SymbolicTrace)] -> [SymbolicTrace]
analyseContractAux [] = []
analyseContractAux ((c,st):t) = st:(analyseContractAux (t ++ (extractSymbolicTraces st (analyseContractStep c))))

extractBlockNum :: SymbolicTrace -> SymbolicTrace
extractBlockNum (s@(SymbolicTrace {constraints = cons, currentBlock = var})) =
  s {constraints = And ([generateEq [Var $ CurrentBlock] var,
                         Eq $ LE [Const 0] [Var $ CurrentBlock], cons] ++
                        [Eq $ LE [Const 0] [Var $ el] | el@(InputIssueBlock _) <- collectVars cons])}

reverseExplanation :: SymbolicTrace -> SymbolicTrace
reverseExplanation (s@(SymbolicTrace {explanation = expl})) = s {explanation = reverse expl}

analyseContract :: Contract -> [SymbolicTrace]
analyseContract c = map (reverseExplanation . extractBlockNum) $ analyseContractAux [(c, emptySymbolicTrace)]

printExplanation :: (Integer, [Explanation]) -> IO ()
printExplanation (n, []) = do putStrLn ("Trace " ++ show n ++ ":")
                              putStrLn (" - Do nothing.")
printExplanation (n, l) = do putStrLn ("Trace " ++ show n ++ ":")
                             mapM_ (\x -> putStrLn (" - " ++ x)) l

explainPossibleSymbolicTraces :: Contract -> IO ()
explainPossibleSymbolicTraces c = mapM_ printExplanation posRes
  where
    res = analyseContract c
    posRes = map (\(n, s) -> (n, explanation s)) $ zip [1..] $ filter (isJust . symbolicToConcreteTrace) res

{----------------------
 - Auxiliar functions -
 ----------------------}

constant :: Integer -> VarExpr
constant x = [Const $ x]

generateAV :: Integer -> (Integer, VarExpr)
generateAV x = (x + 1, [Var $ TempVar x])

generateEq :: VarExpr -> VarExpr -> SLogic 
generateEq x y = And [Eq $ LE x y, Eq $ LE y x]

symIsExpired :: VarExpr -> VarExpr -> SLogic
symIsExpired e ee = Eq $ LE ee e

ifThenElseSymTV :: SLogic -> VarExpr -> VarExpr -> SE VarExpr
ifThenElseSymTV cond xv yv =
  do nv <- newVar 
     addConstraint $ Or [And [generateEq nv xv, xl], And [generateEq nv yv, yl]]
     return nv 
  where
    xl = cond
    yl = Not cond

ifThenElseSymTVL :: SLogic -> [VarExpr] -> [VarExpr] -> SE [VarExpr]
ifThenElseSymTVL cond xv yv =
  if xlen /= ylen then error "Different length lists in ifThenElseSymTVL"
  else (do nv <- replicateM xlen newVar
           addConstraint $ Or [And (xl:[generateEq anv axv | (axv, anv) <- zip xv nv]),
                               And (yl:[generateEq anv ayv | (ayv, anv) <- zip yv nv])]
           return nv)
  where
    xlen = length xv
    ylen = length yv
    xl = cond
    yl = Not cond

symIfExpiredTV :: VarExpr -> VarExpr -> VarExpr -> SE VarExpr
symIfExpiredTV expi f1 f2 =
  do bn <- getBlockNum
     ifThenElseSymTV (symIsExpired bn expi) f1 f2

symIfExpired :: VarExpr -> SE a -> SE a -> SE a
symIfExpired expi f1 f2 =
   do bn <- getBlockNum
      ifThenElseSymb (symIsExpired bn expi) f1 f2

