{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Marlowe.Analysis.FSSemanticsFast where

import           Data.List       (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Set        (Set)
import qualified Data.Set        as S
import           Data.Maybe      (isNothing)
import           Data.SBV
import           Data.SBV.Internals (SMTModel(..))
import qualified Data.SBV.Tuple as ST
import qualified Data.SBV.Either as SE
import qualified Data.SBV.Maybe as SM
import qualified Data.SBV.List as SL
import           Language.Marlowe.Semantics

data SymInput = SymDeposit AccountId Party {- Token -} SInteger
              | SymChoice ChoiceId SInteger
              | SymNotify

data SymState = SymState { lowSlot :: SInteger
                         , highSlot :: SInteger
                         , traces :: [(SInteger, SInteger, Maybe SymInput, Integer)]
                         , symAccounts :: Map AccountId SInteger
                         , symChoices :: Map ChoiceId SInteger
                         , symBoundValues :: Map ValueId SInteger
                         }

emptySymState :: Symbolic SymState
emptySymState = do hs <- sInteger_
                   ls <- sInteger_
                   constrain (ls .<= hs)
                   return $ SymState { lowSlot = ls
                                     , highSlot = hs
                                     , traces = []
                                     , symAccounts = M.empty
                                     , symChoices = M.empty
                                     , symBoundValues = M.empty }

type Trace = Integer 
type STrace = SBV Trace

convertToSymbolicTrace :: [(SInteger, SInteger, Maybe SymInput, Integer)] -> STrace
convertToSymbolicTrace tra = literal 0

symEvalVal :: Value -> SymState -> SInteger
symEvalVal (AvailableMoney accId {- tok -}) symState =
  M.findWithDefault (literal 0) accId (symAccounts symState)
symEvalVal (Constant inte) symState = literal inte
symEvalVal (NegValue val) symState = (- symEvalVal val symState)
symEvalVal (AddValue lhs rhs) symState = (symEvalVal lhs symState) +
                                         (symEvalVal rhs symState)
symEvalVal (SubValue lhs rhs) symState = (symEvalVal lhs symState) -
                                         (symEvalVal rhs symState)
symEvalVal (ChoiceValue choId defVal) symState =
  M.findWithDefault (symEvalVal defVal symState) choId (symChoices symState)
symEvalVal SlotIntervalStart symState = lowSlot symState
symEvalVal SlotIntervalEnd symState = highSlot symState
symEvalVal (UseValue valId) symState =
  M.findWithDefault (literal 0) valId (symBoundValues symState)


symEvalObs :: Observation -> SymState -> SBool
symEvalObs (AndObs obs1 obs2) symState = (symEvalObs obs1 symState) .&&
                                         (symEvalObs obs2 symState)
symEvalObs (OrObs obs1 obs2) symState = (symEvalObs obs1 symState) .||
                                        (symEvalObs obs2 symState)
symEvalObs (NotObs obs) symState = sNot $ symEvalObs obs symState
symEvalObs (ChoseSomething choiceId) symState =
  literal (M.member choiceId (symChoices symState))
symEvalObs (ValueGE lhs rhs) symState = (symEvalVal lhs symState) .>=
                                        (symEvalVal rhs symState)
symEvalObs (ValueGT lhs rhs) symState = (symEvalVal lhs symState) .>
                                        (symEvalVal rhs symState)
symEvalObs (ValueLT lhs rhs) symState = (symEvalVal lhs symState) .<
                                        (symEvalVal rhs symState)
symEvalObs (ValueLE lhs rhs) symState = (symEvalVal lhs symState) .<=
                                        (symEvalVal rhs symState)
symEvalObs (ValueEQ lhs rhs) symState = (symEvalVal lhs symState) .==
                                        (symEvalVal rhs symState)
symEvalObs TrueObs _ = sTrue
symEvalObs FalseObs _ = sFalse

updateSymInput :: Maybe SymInput -> SymState -> Symbolic SymState
updateSymInput Nothing symState = return symState
updateSymInput (Just (SymDeposit accId _ val)) symState =
  let resultVal = M.findWithDefault 0 accId (symAccounts symState)
                   + smax (literal 0) val in
  return (symState {symAccounts = M.insert accId resultVal 
                                           (symAccounts symState)})
updateSymInput (Just (SymChoice choId val)) symState =
  return (symState {symChoices = M.insert choId val (symChoices symState)})
updateSymInput (Just SymNotify) symState = return symState

addTransaction :: Maybe SymInput -> Timeout -> SymState -> Integer
               -> Symbolic (SBool, SymState)
addTransaction symInput slotTim (symState@(SymState { lowSlot = oldLowSlot
                                                    , highSlot = oldHighSlot
                                                    , traces = oldTraces })) pos =
  do let tim = getSlot slotTim
     newLowSlot <- sInteger_
     newHighSlot <- sInteger_
     constrain (newLowSlot .<= newHighSlot)
     let conditions =
           (if (isNothing symInput)
            then ((oldHighSlot .< literal tim) .||
                  ((oldLowSlot .== newLowSlot) .&& (oldHighSlot .== newHighSlot))) .&&
                 (newLowSlot .>= literal tim)
            else ((oldHighSlot .< literal tim) .&&
                  (newHighSlot .< literal tim) .&&
                  (newLowSlot .>= oldLowSlot)))
     uSymInput <- updateSymInput symInput
                                (symState { lowSlot = newLowSlot
                                          , highSlot = newHighSlot
                                          , traces = (oldLowSlot, oldHighSlot, symInput, pos)
                                                     :oldTraces })
     return (conditions, uSymInput)

isValidAndFailsAux :: Contract -> SymState
                   -> Symbolic (SMaybe Trace)
isValidAndFailsAux Close sState = 
  do return $ SM.sNothing
isValidAndFailsAux (Pay accId payee {- token -} val cont) sState =
  do let concVal = symEvalVal val sState
     let potentialFailedPayTrace =
          convertToSymbolicTrace ((lowSlot sState, highSlot sState, Nothing, 0)
                                  :(traces sState))
     let originalMoney = M.findWithDefault 0 accId (symAccounts sState)
     let remainingMoneyInAccount = originalMoney - concVal
     let newAccs = M.insert accId (smax (literal 0) remainingMoneyInAccount)
                            (symAccounts sState)
     let finalSState = sState { symAccounts =
           case payee of
             (Account destAccId) ->
                M.insert accId
                         (smin originalMoney (smax (literal 0) concVal)
                            + M.findWithDefault 0 destAccId newAccs)
                         newAccs
             _ -> newAccs }
     contRes <- isValidAndFailsAux cont finalSState
     return (ite ((remainingMoneyInAccount .< 0) .|| (concVal .<= 0))
                 (SM.sJust potentialFailedPayTrace)
                 contRes)
isValidAndFailsAux (If obs cont1 cont2) sState =
  do let obsVal = symEvalObs obs sState
     contVal1 <- isValidAndFailsAux cont1 sState
     contVal2 <- isValidAndFailsAux cont2 sState
     return (ite obsVal contVal1 contVal2)
isValidAndFailsAux (When list timeout cont) sState =
  isValidAndFailsWhen list timeout cont (const sFalse) sState 1
isValidAndFailsAux (Let valId val cont) sState =
  do let concVal = symEvalVal val sState
     let newBVMap = M.insert valId concVal (symBoundValues sState)
     let newSState = sState { symBoundValues = newBVMap }
     isValidAndFailsAux cont newSState

ensureBounds :: SInteger -> [Bound] -> Symbolic ()
ensureBounds cho [] = return ()
ensureBounds cho ((Bound lowBnd hiBnd):t) =
  do constrain (cho .>= literal lowBnd)
     constrain (cho .<= literal hiBnd)

generateValueInBounds :: [Bound] -> Symbolic SInteger
generateValueInBounds bnds =
  do bnd <- sInteger_
     ensureBounds bnd bnds
     return bnd

isValidAndFailsWhen :: [Case] -> Timeout -> Contract -> (SymInput -> SBool) -> SymState
                    -> Integer -> Symbolic (SMaybe Trace) 
isValidAndFailsWhen [] timeout cont previousMatch sState pos =
  do (cond, newSState) <- addTransaction Nothing timeout sState 0
     newTrace <- (isValidAndFailsAux cont newSState)
     return (ite cond newTrace SM.sNothing)
isValidAndFailsWhen ((Case (Deposit accId party {- token -} val) cont):rest)
                    timeout timCont previousMatch sState pos =
  do let concVal = symEvalVal val sState
     let symInput = SymDeposit accId party {- token -} concVal
     let clashResult = previousMatch symInput
     let newPreviousMatch otherSymInput =
           case otherSymInput of
             SymDeposit otherAccId otherParty {- otherToken -} otherConcVal ->
               if ((otherAccId == accId) && (otherParty == party)
                   {- && (otherToken == token) -})
               then ((otherConcVal .== concVal) .|| (previousMatch otherSymInput))
               else previousMatch otherSymInput
             _ -> previousMatch otherSymInput
     (newCond, newSState) <- addTransaction (Just symInput) timeout sState pos
     newTrace <- isValidAndFailsAux cont newSState
     contTrace <- isValidAndFailsWhen rest timeout timCont newPreviousMatch sState (pos + 1)
     return (ite (newCond .&& (SM.isJust newTrace)) newTrace contTrace)
isValidAndFailsWhen ((Case (Choice choId bnds) cont):rest)
                    timeout timCont previousMatch sState pos =
  do concVal <- generateValueInBounds bnds 
     let symInput = SymChoice choId concVal
     let clashResult = previousMatch symInput
     let newPreviousMatch otherSymInput =
           case otherSymInput of
             SymChoice otherChoId otherConcVal ->
               if (otherChoId == choId)
               then ((otherConcVal .== concVal) .|| (previousMatch otherSymInput))
               else previousMatch otherSymInput
             _ -> previousMatch otherSymInput
     (newCond, newSState) <- addTransaction (Just symInput) timeout sState pos
     newTrace <- isValidAndFailsAux cont newSState
     contTrace <- isValidAndFailsWhen rest timeout timCont newPreviousMatch sState (pos + 1)
     return (ite (newCond .&& (SM.isJust newTrace)) newTrace contTrace)
isValidAndFailsWhen ((Case (Notify obs) cont):rest)
                    timeout timCont previousMatch sState pos =
  do let obsRes = symEvalObs obs sState
     let symInput = SymNotify
     let clashResult = previousMatch symInput
     let newPreviousMatch otherSymInput =
           case otherSymInput of
             SymNotify -> sNot obsRes 
             _ -> previousMatch otherSymInput
     (newCond, newSState) <- addTransaction (Just symInput) timeout sState pos
     newTrace <- isValidAndFailsAux cont newSState
     contTrace <- isValidAndFailsWhen rest timeout timCont newPreviousMatch sState (pos + 1)
     return (ite (newCond .&& obsRes .&& (SM.isJust newTrace)) newTrace contTrace)

isValidAndFails :: Contract -> Symbolic (SMaybe Trace)
isValidAndFails contract = do ess <- emptySymState
                              isValidAndFailsAux contract ess

wrapper :: Contract -> Symbolic SBool
wrapper c = do r <- isValidAndFails c
               return (SM.isJust r)

