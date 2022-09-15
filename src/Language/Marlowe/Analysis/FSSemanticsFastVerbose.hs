{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Marlowe.Analysis.FSSemanticsFastVerbose (
    warningsTrace'
  , warningsTrace
  ) where

import           Data.ByteString (ByteString)
import           Data.List                       (foldl')
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as M
import           Data.SBV
import           Data.SBV.Internals              (SMTModel (..))
import           Language.Marlowe.Semantics
import           Language.Marlowe.Semantics.Types
import           Language.Marlowe.Semantics.Deserialisation (byteStringToContract)

---------------------------------------------------
-- Static analysis logic and symbolic operations --
---------------------------------------------------

-- Symbolic version of Input (with symbolic value but concrete identifiers)
data SymInput i t = SymDeposit (Party i) (Party i) t SInteger
                  | SymChoice (ChoiceId i) SInteger
                  | SymNotify

-- Symbolic version of State:
-- We keep as much things concrete as possible.
-- In addition to normal State information we also store symbolic values that
-- represent the symbolic trace we are evaluating (the way we got to the current
-- part of the contract).
--
-- Symbolic trace is composed of:
--
-- *** Current transaction info
-- lowTime, highTime -- time interval for the most recent transaction
-- symInput -- input for the most recent transaction
-- whenPos -- position in the When for the most recen transaction (see trace and paramTrace)
--
-- *** Previous transaction info
-- traces -- symbolic information about previous transactions (when we reach a When we
--           consider adding the current transaction to this list)
--           first integer is lowTime, second is highTime, last integer is the position in
--           the When (which case of the When the input corresponds to 0 is timeout)
-- *** Input parameter transaction info
-- paramTrace -- this is actually an input parameter, we get it as input for the SBV
--               property and we constrain it to match traces for any of the executions,
--               SBV will try to find a paramTrace that matches, and that will be the
--               solution to the analysis (the counterexample if any). It has a fixed
--               length that is calculated as the maximum bound given by countWhens,
--               which is the maximum number of transactions that are necessary to explore
--               the whole contract. This bound is proven in TransactionBound.thy
--
-- The rest of the symbolic state just corresponds directly to State with symbolic values:
-- symAccounts, symChoices, and symBoundValues
--
-- minTime just corresponds to lowTime, because it is just a lower bound for the minimum
-- time, and it gets updated with the minimum time.
data SymState i t = SymState { lowTime        :: SInteger
                             , highTime       :: SInteger
                             , traces         :: [(SInteger, SInteger, Maybe (SymInput i t), Integer)]
                             , paramTrace     :: [(SInteger, SInteger, SInteger, SInteger)]
                             , symInput       :: Maybe (SymInput i t)
                             , whenPos        :: Integer
                             , symAccounts    :: Map (Party i, t) SInteger
                             , symChoices     :: Map (ChoiceId i) SInteger
                             , symBoundValues :: Map ValueId SInteger
                             }

-- It generates a valid symbolic interval with lower bound ms (if provided)
generateSymbolicInterval :: Maybe Integer -> Symbolic (SInteger, SInteger)
generateSymbolicInterval Nothing =
  do hs <- sInteger_
     ls <- sInteger_
     constrain (ls .<= hs)
     return (ls, hs)
generateSymbolicInterval (Just ms) =
  do i@(ls, _) <- generateSymbolicInterval Nothing
     constrain (ls .>= literal ms)
     return i

-- foldWithKey for Plutus' AssocMap
foldAssocMapWithKey :: (a -> k -> b -> a) -> a -> Map k b -> a
foldAssocMapWithKey f acc = foldl' decF acc . M.toList
  where decF a (k, v) = f a k v

-- Convert Plutus' AssocMap into a Map with symbolic values, which are literals of
-- the content of the original AssocMap
toSymMap :: Ord k => SymVal v => Map k v -> Map k (SBV v)
toSymMap = foldAssocMapWithKey toSymItem mempty
  where toSymItem :: Ord k => SymVal v => Map k (SBV v) -> k -> v -> Map k (SBV v)
        toSymItem acc k v = M.insert k (literal v) acc

-- Create initial symbolic state, it takes an optional concrete State to serve
-- as initial state, this way analysis can be done from a half-executed contract.
-- First parameter (pt) is the input parameter trace, which is just a fixed length
-- list of symbolic integers that are matched to trace.
-- When Nothing is passed as second parameter it acts like emptyState.
mkInitialSymState :: (Ord i, Ord t)
                  => [(SInteger, SInteger, SInteger, SInteger)] -> Maybe (State i t)
                  -> Symbolic (SymState i t)
mkInitialSymState pt Nothing = do (ls, hs) <- generateSymbolicInterval Nothing
                                  return $ SymState { lowTime = ls
                                                    , highTime = hs
                                                    , traces = []
                                                    , paramTrace = pt
                                                    , symInput = Nothing
                                                    , whenPos = 0
                                                    , symAccounts = mempty
                                                    , symChoices = mempty
                                                    , symBoundValues = mempty }
mkInitialSymState pt (Just State { accounts = accs
                                 , choices = cho
                                 , boundValues = bVal
                                 , minTime = ms }) =
  do (ls, hs) <- generateSymbolicInterval (Just (getPOSIXTime ms))
     return $ SymState { lowTime = ls
                       , highTime = hs
                       , traces = []
                       , paramTrace = pt
                       , symInput = Nothing
                       , whenPos = 0
                       , symAccounts = toSymMap accs
                       , symChoices = toSymMap cho
                       , symBoundValues = toSymMap bVal }

-- It converts a symbolic trace into a list of 4-uples of symbolic integers,
-- this is a minimalistic representation of the counter-example trace that aims
-- to minimise the functionalities from SBV that we use (just integers) for efficiency.
-- The integers in the tuple represent:
-- 1st - time interval min time
-- 2nd - time interval max time
-- 3rd - When clause used (0 for timeout branch)
-- 4rd - Symbolic value (money in deposit, chosen value in choice)
--
-- Because the param trace has fixed length we fill the unused transactions with -1,
-- these are pruned after analysis.
--
-- The identifiers for Deposit and Choice are calculated using the When clause and
-- the contract (which is concrete), and using the semantics after a counter example is
-- found.
convertToSymbolicTrace :: [(SInteger, SInteger, Maybe (SymInput i t), Integer)] ->
                          [(SInteger, SInteger, SInteger, SInteger)] -> SBool
convertToSymbolicTrace [] [] = sTrue
convertToSymbolicTrace [] ((a, b, c, d):t) = (a .== -1) .&& (b .== -1) .&& (c .== -1) .&&
                                             (d .== -1) .&& convertToSymbolicTrace [] t
convertToSymbolicTrace ((lowS, highS, inp, pos):t) ((a, b, c, d):t2) =
  (lowS .== a) .&& (highS .== b) .&& (getSymValFrom inp .== c) .&& (literal pos .== d) .&&
  convertToSymbolicTrace t t2
  where
    getSymValFrom :: Maybe (SymInput i t) -> SInteger
    getSymValFrom Nothing                     = 0
    getSymValFrom (Just (SymDeposit _ _ _ val)) = val
    getSymValFrom (Just (SymChoice _ val))    = val
    getSymValFrom (Just SymNotify)            = 0
convertToSymbolicTrace _ _ = error "Provided symbolic trace is not long enough"

-- Symbolic version evalValue
symEvalVal :: (Ord i, Ord t) => Value i t -> SymState i t -> SInteger
symEvalVal (AvailableMoney accId tok) symState =
  M.findWithDefault (literal 0) (accId, tok) (symAccounts symState)
symEvalVal (Constant inte) _symState = literal inte
symEvalVal (NegValue val) symState = - symEvalVal val symState
symEvalVal (AddValue lhs rhs) symState = symEvalVal lhs symState +
                                         symEvalVal rhs symState
symEvalVal (SubValue lhs rhs) symState = symEvalVal lhs symState -
                                         symEvalVal rhs symState
symEvalVal (MulValue lhs rhs) symState = symEvalVal lhs symState *
                                         symEvalVal rhs symState
symEvalVal (DivValue lhs rhs) symState =
  let n = symEvalVal lhs symState
      d = symEvalVal rhs symState
  in ite (d .== 0) 0 (n `sQuot` d)
symEvalVal (ChoiceValue choId) symState =
  M.findWithDefault (literal 0) choId (symChoices symState)
symEvalVal TimeIntervalStart symState = lowTime symState
symEvalVal TimeIntervalEnd symState = highTime symState
symEvalVal (UseValue valId) symState =
  M.findWithDefault (literal 0) valId (symBoundValues symState)
symEvalVal (Cond cond v1 v2) symState = ite (symEvalObs cond symState)
                                            (symEvalVal v1 symState)
                                            (symEvalVal v2 symState)

-- Symbolic version evalObservation
symEvalObs :: (Ord i, Ord t) => Observation i t -> SymState i t -> SBool
symEvalObs (AndObs obs1 obs2) symState = symEvalObs obs1 symState .&&
                                         symEvalObs obs2 symState
symEvalObs (OrObs obs1 obs2) symState = symEvalObs obs1 symState .||
                                        symEvalObs obs2 symState
symEvalObs (NotObs obs) symState = sNot $ symEvalObs obs symState
symEvalObs (ChoseSomething choiceId) symState =
  literal (M.member choiceId (symChoices symState))
symEvalObs (ValueGE lhs rhs) symState = symEvalVal lhs symState .>=
                                        symEvalVal rhs symState
symEvalObs (ValueGT lhs rhs) symState = symEvalVal lhs symState .>
                                        symEvalVal rhs symState
symEvalObs (ValueLT lhs rhs) symState = symEvalVal lhs symState .<
                                        symEvalVal rhs symState
symEvalObs (ValueLE lhs rhs) symState = symEvalVal lhs symState .<=
                                        symEvalVal rhs symState
symEvalObs (ValueEQ lhs rhs) symState = symEvalVal lhs symState .==
                                        symEvalVal rhs symState
symEvalObs TrueObs _ = sTrue
symEvalObs FalseObs _ = sFalse

-- Update the symbolic state given a symbolic input (just the maps)
updateSymInput :: (Ord i, Ord t) => Maybe (SymInput i t) -> SymState i t -> Symbolic (SymState i t)
updateSymInput Nothing symState = return symState
updateSymInput (Just (SymDeposit accId _ tok val)) symState =
  let resultVal = M.findWithDefault 0 (accId, tok) (symAccounts symState)
                   + smax (literal 0) val in
  return (symState {symAccounts =
                       M.insert (accId, tok) resultVal
                                (symAccounts symState)})
updateSymInput (Just (SymChoice choId val)) symState =
  return (symState {symChoices = M.insert choId val (symChoices symState)})
updateSymInput (Just SymNotify) symState = return symState

-- Moves the current transaction to the list of transactions and creates a
-- new one. It takes newLowTime and newHighTime as parameters because the
-- values and observations are evaluated using those, so we cannot just generate
-- them here (they are linked to the SymInput (3rd parameter).
-- If SymInput is Nothing it means the transaction went to timeout.
-- If the transaction didn't go to timeout, we know the new transaction has maxTime smaller
-- than timeout. If it went to timeout we know the new transaction has minTime greater or
-- equal than timeout. We also need to check previous transaction does not have ambiguous
-- interval with the current When, because that would mean the transaction is invalid.
-- In the case of timeout it is possible we don't actually need a new transaction,
-- we can reuse the previous transaction, we model this by allowing both low and high
-- time to be equal to the ones of the previous transaction. That will typically make one
-- of the transactions useless, but we discard useless transactions by the end so that
-- is fine.
addTransaction :: (Ord i, Ord t)
               => SInteger -> SInteger -> Maybe (SymInput i t) -> Timeout -> SymState i t -> Integer
               -> Symbolic (SBool, SymState i t)
addTransaction newLowTime newHighTime Nothing timeTim
               symState@SymState { lowTime = oldLowTime
                                 , highTime = oldHighTime
                                 , traces = oldTraces
                                 , symInput = prevSymInp
                                 , whenPos = oldPos } pos =
  do let tim = getPOSIXTime timeTim
     constrain (newLowTime .<= newHighTime)
     let conditions = ((oldHighTime .< literal tim) .||
                      ((oldLowTime .== newLowTime) .&& (oldHighTime .== newHighTime))) .&&
                      (newLowTime .>= literal tim)
     uSymInput <- updateSymInput Nothing
                                 (symState { lowTime = newLowTime
                                           , highTime = newHighTime
                                           , traces = (oldLowTime, oldHighTime,
                                                       prevSymInp, oldPos):oldTraces
                                           , symInput = Nothing
                                           , whenPos = pos })
     return (conditions, uSymInput)
addTransaction newLowTime newHighTime newSymInput timeTim
               symState@SymState { lowTime = oldLowTime
                                 , highTime = oldHighTime
                                 , traces = oldTraces
                                 , symInput = prevSymInp
                                 , whenPos = oldPos } pos =
  do let tim = getPOSIXTime timeTim
     constrain (newLowTime .<= newHighTime)
     let conditions = (oldHighTime .< literal tim) .&&
                      (newHighTime .< literal tim) .&&
                      (newLowTime .>= oldLowTime)
     uSymInput <- updateSymInput newSymInput
                        (symState { lowTime = newLowTime
                                  , highTime = newHighTime
                                  , traces = (oldLowTime, oldHighTime, prevSymInp, oldPos)
                                             :oldTraces
                                  , symInput = newSymInput
                                  , whenPos = pos })
     return (conditions, uSymInput)

-- This is the main static analysis loop for contracts.
-- - hasErr -- indicates whether the current symbolic execution has already
-- raised a warning (this is a necessary condition for it to be a counter-example)
-- - contract -- remaining contract
-- - sState -- symbolic state
--
-- The result of this function is a boolean that indicates whether:
-- 1. The transaction is valid (according to the semantics)
-- 2. It has issued a warning (as indicated by hasErr)
isValidAndFailsAux :: (Ord i, Ord t)
                   => SBool -> Contract i t -> SymState i t
                   -> Symbolic SBool
isValidAndFailsAux hasErr Close sState =
  return (hasErr .&& convertToSymbolicTrace ((lowTime sState, highTime sState,
                                              symInput sState, whenPos sState)
                                              :traces sState) (paramTrace sState))
isValidAndFailsAux hasErr (Pay accId payee token val cont) sState =
  do let concVal = symEvalVal val sState
     let originalMoney = M.findWithDefault 0 (accId, token) (symAccounts sState)
     let remainingMoneyInAccount = originalMoney - smax (literal 0) concVal
     let newAccs = M.insert (accId, token) (smax (literal 0) remainingMoneyInAccount)
                                  (symAccounts sState)
     let finalSState = sState { symAccounts =
           case payee of
             (Account destAccId) ->
                M.insert (destAccId, token)
                         (smin originalMoney (smax (literal 0) concVal)
                            + M.findWithDefault 0 (destAccId, token) newAccs)
                         newAccs
             _ -> newAccs }
     isValidAndFailsAux ((remainingMoneyInAccount .< 0) -- Partial payment
                         .|| (concVal .<= 0) -- Non-positive payment
                         .|| hasErr) cont finalSState
isValidAndFailsAux hasErr (If obs cont1 cont2) sState =
  do let obsVal = symEvalObs obs sState
     contVal1 <- isValidAndFailsAux hasErr cont1 sState
     contVal2 <- isValidAndFailsAux hasErr cont2 sState
     return (ite obsVal contVal1 contVal2)
isValidAndFailsAux hasErr (When list timeout cont) sState =
  isValidAndFailsWhen hasErr list timeout cont (const $ const sFalse) sState 1
isValidAndFailsAux hasErr (Let valId val cont) sState =
  do let concVal = symEvalVal val sState
     let newBVMap = M.insert valId concVal (symBoundValues sState)
     let newSState = sState { symBoundValues = newBVMap }
     isValidAndFailsAux ((literal (M.member valId (symBoundValues sState))) -- Shadowed definition
                         .|| hasErr) cont newSState
isValidAndFailsAux hasErr (Assert obs cont) sState =
  isValidAndFailsAux (hasErr .|| sNot obsVal) cont sState
  where obsVal = symEvalObs obs sState

-- Returns sTrue iif the given sinteger is in the list of bounds
ensureBounds :: SInteger -> [Bound] -> SBool
ensureBounds _cho [] = sFalse
ensureBounds  cho (Bound lowBnd hiBnd:t) =
    ((cho .>= literal lowBnd) .&& (cho .<= literal hiBnd)) .|| ensureBounds cho t

-- Just combines addTransaction and isValidAndFailsAux
applyInputConditions :: (Ord i, Ord t)
                     => SInteger -> SInteger -> SBool -> Maybe (SymInput i t) -> Timeout
                     -> SymState i t -> Integer -> Contract i t
                     -> Symbolic (SBool, SBool)
applyInputConditions ls hs hasErr maybeSymInput timeout sState pos cont =
  do (newCond, newSState) <- addTransaction ls hs maybeSymInput timeout sState pos
     newTrace <- isValidAndFailsAux hasErr cont newSState
     return (newCond, newTrace)

-- Generates two new time numbers and puts them in the symbolic state
addFreshTimesToState :: SymState i t -> Symbolic (SInteger, SInteger, SymState i t)
addFreshTimesToState sState =
  do newLowTime <- sInteger_
     newHighTime <- sInteger_
     return (newLowTime, newHighTime, sState {lowTime = newLowTime, highTime = newHighTime})

-- Analysis loop for When construct. Essentially, it iterates over all the cases and
-- branches the static analysis. All parameters are the same as isValidAndFailsAux except
-- for previousMatch and pos:
-- - previousMatch - Is a function that tells whether some previous case has matched, if
-- that happened then the current case would never be reached, we keep adding conditions
-- to the function and pass it to the next iteration of isValidAndFailsWhen.
-- - pos - Is the position of the current Case clause [1..], 0 means timeout branch.
isValidAndFailsWhen :: (Ord i, Ord t)
                    => SBool -> [Case i t] -> Timeout -> Contract i t -> (SymInput i t -> SymState i t -> SBool)
                    -> SymState i t -> Integer -> Symbolic SBool
isValidAndFailsWhen hasErr [] timeout cont _previousMatch sState _pos =
  do newLowTime <- sInteger_
     newHighTime <- sInteger_
     (cond, newTrace)
               <- applyInputConditions newLowTime newHighTime
                                       hasErr Nothing timeout sState 0 cont
     return (ite cond newTrace sFalse)
isValidAndFailsWhen hasErr (Case (Deposit accId party token val) cont:rest)
                    timeout timCont previousMatch sState pos =
  do (newLowTime, newHighTime, sStateWithInput) <- addFreshTimesToState sState
     let concVal = symEvalVal val sStateWithInput
     let symInput = SymDeposit accId party token concVal
     let clashResult = previousMatch symInput sStateWithInput
     let newPreviousMatch otherSymInput pmSymState =
           let pmConcVal = symEvalVal val pmSymState in
           case otherSymInput of
             SymDeposit otherAccId otherParty otherToken otherConcVal ->
               if (otherAccId == accId) && (otherParty == party) && (otherToken == token)
               then (otherConcVal .== pmConcVal) .|| previousMatch otherSymInput pmSymState
               else previousMatch otherSymInput pmSymState
             _ -> previousMatch otherSymInput pmSymState
     (newCond, newTrace)
               <- applyInputConditions newLowTime newHighTime
                      (hasErr .|| (concVal .<= 0)) -- Non-positive deposit warning
                      (Just symInput) timeout sState pos cont
     contTrace <- isValidAndFailsWhen hasErr rest timeout timCont
                                      newPreviousMatch sState (pos + 1)
     return (ite (newCond .&& sNot clashResult) newTrace contTrace)
isValidAndFailsWhen hasErr (Case (Choice choId bnds) cont:rest)
                    timeout timCont previousMatch sState pos =
  do (newLowTime, newHighTime, sStateWithInput) <- addFreshTimesToState sState
     concVal <- sInteger_
     let symInput = SymChoice choId concVal
     let clashResult = previousMatch symInput sStateWithInput
     let newPreviousMatch otherSymInput pmSymState =
           case otherSymInput of
             SymChoice otherChoId otherConcVal ->
               if otherChoId == choId
               then ensureBounds otherConcVal bnds .|| previousMatch otherSymInput pmSymState
               else previousMatch otherSymInput pmSymState
             _ -> previousMatch otherSymInput pmSymState
     contTrace <- isValidAndFailsWhen hasErr rest timeout timCont
                                      newPreviousMatch sState (pos + 1)
     (newCond, newTrace)
               <- applyInputConditions newLowTime newHighTime
                                       hasErr (Just symInput) timeout sState pos cont
     return (ite (newCond .&& sNot clashResult)
                 (ensureBounds concVal bnds .&& newTrace)
                 contTrace)
isValidAndFailsWhen hasErr (Case (Notify obs) cont:rest)
                    timeout timCont previousMatch sState pos =
  do (newLowTime, newHighTime, sStateWithInput) <- addFreshTimesToState sState
     let obsRes = symEvalObs obs sStateWithInput
     let symInput = SymNotify
     let clashResult = previousMatch symInput sStateWithInput
     let newPreviousMatch otherSymInput pmSymState =
           let pmObsRes = symEvalObs obs pmSymState in
           case otherSymInput of
             SymNotify -> pmObsRes .|| previousMatch otherSymInput pmSymState
             _         -> previousMatch otherSymInput pmSymState
     contTrace <- isValidAndFailsWhen hasErr rest timeout timCont
                                      newPreviousMatch sState (pos + 1)
     (newCond, newTrace)
               <- applyInputConditions newLowTime newHighTime
                                       hasErr (Just symInput) timeout sState pos cont
     return (ite (newCond .&& obsRes .&& sNot clashResult) newTrace contTrace)
isValidAndFailsWhen hasErr (MerkleizedCase (Deposit accId party token val) _:rest)
                    timeout timCont previousMatch sState pos =
    let newPreviousMatch otherSymInput pmSymState =
           let pmConcVal = symEvalVal val pmSymState in
           case otherSymInput of
             SymDeposit otherAccId otherParty otherToken otherConcVal ->
               if (otherAccId == accId) && (otherParty == party) && (otherToken == token)
               then (otherConcVal .== pmConcVal) .|| previousMatch otherSymInput pmSymState
               else previousMatch otherSymInput pmSymState
             _ -> previousMatch otherSymInput pmSymState in
     isValidAndFailsWhen hasErr rest timeout timCont
                         newPreviousMatch sState (pos + 1)
isValidAndFailsWhen hasErr (MerkleizedCase (Choice choId bnds) _:rest)
                    timeout timCont previousMatch sState pos =
     let newPreviousMatch otherSymInput pmSymState =
           case otherSymInput of
             SymChoice otherChoId otherConcVal ->
               if otherChoId == choId
               then ensureBounds otherConcVal bnds .|| previousMatch otherSymInput pmSymState
               else previousMatch otherSymInput pmSymState
             _ -> previousMatch otherSymInput pmSymState in
     isValidAndFailsWhen hasErr rest timeout timCont newPreviousMatch sState (pos + 1)
isValidAndFailsWhen hasErr (MerkleizedCase (Notify obs) _:rest)
                    timeout timCont previousMatch sState pos =
     let newPreviousMatch otherSymInput pmSymState =
           let pmObsRes = symEvalObs obs pmSymState in
           case otherSymInput of
             SymNotify -> pmObsRes .|| previousMatch otherSymInput pmSymState
             _         -> previousMatch otherSymInput pmSymState in
     isValidAndFailsWhen hasErr rest timeout timCont
                                      newPreviousMatch sState (pos + 1)

--------------------------------------------------
-- Wrapper - SBV handling and result extraction --
--------------------------------------------------

-- Counts the maximum number of nested Whens. This acts as a bound for the maximum
-- necessary number of transactions for exploring the whole contract. This bound
-- has been proven in TransactionBound.thy
countWhens :: Contract i t -> Integer
countWhens Close                   = 0
countWhens (Pay _uv _uw _ux _uy c) = countWhens c
countWhens (If _uz c c2)           = max (countWhens c) (countWhens c2)
countWhens (When cl _t c)          = 1 + max (countWhensCaseList cl) (countWhens c)
countWhens (Let _va _vb c)         = countWhens c
countWhens (Assert _o c)           = countWhens c

-- Same as countWhens but it starts with a Case list
countWhensCaseList :: [Case i t] -> Integer
countWhensCaseList (Case _uu c : tail)            = max (countWhens c) (countWhensCaseList tail)
countWhensCaseList (MerkleizedCase _uu _c : tail) = countWhensCaseList tail
countWhensCaseList []                             = 0

-- Main wrapper of the static analysis takes a Contract, a paramTrace, and an optional
-- State. paramTrace is actually an output parameter. We do not put it in the result of
-- this function because then we would have to return a symbolic list that would make
-- the whole process slower. It is meant to be used just with SBV, with a symbolic
-- paramTrace, and we use the symbolic paramTrace to know which is the counterexample.
wrapper :: (Ord i, Ord t)
        => Contract i t -> [(SInteger, SInteger, SInteger, SInteger)] -> Maybe (State i t)
        -> Symbolic SBool
wrapper c st maybeState = do ess <- mkInitialSymState st maybeState
                             isValidAndFailsAux sFalse c ess

-- It generates a list of variable names for the variables that conform paramTrace.
-- The list will account for the given number of transactions (four vars per transaction).
generateLabels :: Integer -> [String]
generateLabels = go 1
  where go :: Integer -> Integer -> [String]
        go n m
         | n > m = []
         | otherwise = (action_label ++ "minTime"):
                       (action_label ++ "maxTime"):
                       (action_label ++ "value"):
                       (action_label ++ "branch"):
                       go (n + 1) m
            where action_label = "action_" ++ show n ++ "_"

-- Takes a list of variable names for the paramTrace and generates the list of symbolic
-- variables. It returns the list of symbolic variables generated (list of 4-uples).
generateParameters :: [String] -> Symbolic [(SInteger, SInteger, SInteger, SInteger)]
generateParameters (sl:sh:v:b:t) =
   do isl <- sInteger sl
      ish <- sInteger sh
      iv <- sInteger v
      ib <- sInteger b
      rest <- generateParameters t
      return ((isl, ish, iv, ib):rest)
generateParameters [] = return []
generateParameters _ = error "Wrong number of labels generated"

-- Takes the list of paramTrace variable names and the list of mappings of these
-- names to concrete values, and reconstructs a concrete list of 4-uples of the ordered
-- concrete values.
groupResult :: [String] -> Map String Integer -> [(Integer, Integer, Integer, Integer)]
groupResult (sl:sh:v:b:t) mappings =
    if ib == -1 then []
    else (isl, ish, iv, ib):groupResult t mappings
  where (Just isl) = M.lookup sl mappings
        (Just ish) = M.lookup sh mappings
        (Just iv) = M.lookup v mappings
        (Just ib) = M.lookup b mappings
groupResult [] _ = []
groupResult _ _ = error "Wrong number of labels generated"

-- Reconstructs an input from a Case list a Case position and a value (deposit amount or
-- chosen value)
caseToInput :: [Case i t] -> Integer -> Integer -> Input i t
caseToInput [] _ _ = error "Wrong number of cases interpreting result"
caseToInput (Case h _:t) c v
  | c > 1 = caseToInput t (c - 1) v
  | c == 1 = NormalInput $ case h of
               Deposit accId party tok _ -> IDeposit accId party tok v
               Choice choId _            -> IChoice choId v
               Notify _                  -> INotify
  | otherwise = error "Negative case number"
caseToInput (MerkleizedCase _ _:t) c v
  | c > 1 = caseToInput t (c - 1) v
  | c == 1 = error "Finding this counter example would have required finding a hash preimage"
  | otherwise = error "Negative case number"

-- Given an input, state, and contract, it runs the semantics on the transaction,
-- and it adds the transaction and warnings issued to the result as long as the
-- transaction was not useless. It assumes the transaction is either valid or useless,
-- other errors would mean the counterexample is not valid.
-- Input is passed as a combination and function from input list to transaction input and
-- input list for convenience. The list of 4-uples is passed through because it is used
-- to recursively call executeAndInterpret (co-recursive funtion).
computeAndContinue :: (Ord i, Ord t)
                   => (ByteString -> Maybe (Contract i t, ByteString))
                   -> ([Input i t] -> TransactionInput i t) -> [Input i t] -> State i t -> Contract i t
                   -> [(Integer, Integer, Integer, Integer)]
                   -> [([TransactionInput i t], [TransactionWarning i])]
computeAndContinue decContract transaction inps sta cont t =
  case computeTransaction' decContract (transaction inps) sta cont of
    Error TEUselessTransaction -> executeAndInterpret decContract sta t cont
    Error _ -> error "computeAndContinue: unexpected error"
    TransactionOutput (TOR { txOutWarnings = war
                           , txOutState = newSta
                           , txOutContract = newCont})
                          -> ([transaction inps], war)
                             :executeAndInterpret decContract newSta t newCont

-- Takes a list of 4-uples (and state and contract) and interprets it as a list of
-- transactions and also computes the resulting list of warnings.
executeAndInterpret :: (Ord i, Ord t)
                    => (ByteString -> Maybe (Contract i t, ByteString))
                    -> State i t -> [(Integer, Integer, Integer, Integer)] -> Contract i t
                    -> [([TransactionInput i t], [TransactionWarning i])]
executeAndInterpret _decContract _sta [] _cont = []
executeAndInterpret  decContract sta ((l, h, v, b):t) cont
  | b == 0 = computeAndContinue decContract transaction [] sta cont t
  | otherwise =
       case reduceContractUntilQuiescent env sta cont of
         ContractQuiescent _ _ _ _ tempCont ->
           case tempCont of
             When cases _ _ -> computeAndContinue decContract transaction
                                  [caseToInput cases b v] sta cont t
             _ -> error "Cannot interpret result"
         _ -> error "Error reducing contract when interpreting result"
  where myTimeInterval = TimeInterval (POSIXTime l) (POSIXTime h)
        env = Environment { timeInterval = myTimeInterval }
        transaction inputs = TransactionInput { txInterval = myTimeInterval
                                              , txInputs = inputs
                                              }

-- It wraps executeAndInterpret so that it takes an optional State, and also
-- combines the results of executeAndInterpret in one single tuple.
interpretResult :: (Ord i, Ord t)
                => (ByteString -> Maybe (Contract i t, ByteString))
                -> [(Integer, Integer, Integer, Integer)] -> Contract i t -> Maybe (State i t)
                -> (POSIXTime, [TransactionInput i t], [TransactionWarning i])
interpretResult _decContract [] _ _ = error "Empty result"
interpretResult  decContract t@((l, _h, _v, _b):_) c maybeState = (POSIXTime l, tin, twa)
   where (tin, twa) = foldl' (\(accInp, accWarn) (elemInp, elemWarn) ->
                                 (accInp ++ elemInp, accWarn ++ elemWarn)) ([], []) $
                             executeAndInterpret decContract initialState t c
         initialState = case maybeState of
                          Nothing -> emptyState (POSIXTime l)
                          Just x  -> x

-- It interprets the counter example found by SBV (SMTModel), given the contract,
-- and initial state (optional), and the list of variables used.
extractCounterExample :: (Ord i, Ord t)
                      => (ByteString -> Maybe (Contract i t, ByteString))
                      -> SMTModel -> Contract i t -> Maybe (State i t) -> [String]
                      -> (POSIXTime, [TransactionInput i t], [TransactionWarning i])
extractCounterExample decContract smtModel cont maybeState maps = interpretedResult
  where assocs = map (\(a, b) -> (a, fromCV b :: Integer)) $ modelAssocs smtModel
        counterExample = groupResult maps (M.fromList assocs)
        interpretedResult = interpretResult decContract (reverse counterExample) cont maybeState

-- Wrapper function that carries the static analysis and interprets the result.
-- It generates variables, runs SBV, and it interprets the result in Marlow terms.
warningsTraceWithState ::
                 (Ord i, Ord t)
              => (ByteString -> Maybe (Contract i t, ByteString))
              -> Contract i t
              -> Maybe (State i t)
              -> IO (Either ThmResult
                            (Maybe (POSIXTime, [TransactionInput i t], [TransactionWarning i])))
warningsTraceWithState decContract con maybeState =
    do thmRes@(ThmResult result) <- satCommand
       return (case result of
                 Unsatisfiable _ _ -> Right Nothing
                 Satisfiable _ smtModel ->
                    Right (Just (extractCounterExample decContract smtModel con maybeState params))
                 _ -> Left thmRes)
  where maxActs = 1 + countWhens con
        params = generateLabels maxActs
        property = do v <- generateParameters params
                      r <- wrapper con v maybeState
                      return (sNot r)
        satCommand = proveWith z3 property

-- Like warningsTraceWithState but without initialState.
warningsTrace' :: (Ord i, Ord t)
               => (ByteString -> Maybe (Contract i t, ByteString))
               -> Contract i t
               -> IO (Either ThmResult
                             (Maybe (POSIXTime, [TransactionInput i t], [TransactionWarning i])))
warningsTrace' decContract con = warningsTraceWithState decContract con Nothing


warningsTrace :: Contract ByteString Token
              -> IO (Either ThmResult
                            (Maybe (POSIXTime, [TransactionInput ByteString Token], [TransactionWarning ByteString])))
warningsTrace = warningsTrace' byteStringToContract


