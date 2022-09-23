{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-orphans #-}
module Language.Marlowe.Semantics where

import           Crypto.Hash.SHA256 (hash)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Data.ByteString.Lazy (fromStrict)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import           Data.Ratio (denominator, numerator)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.Leijen (text)
import           Language.Marlowe.Semantics.Deserialisation (byteStringToContract)
import           Language.Marlowe.Semantics.Types (IntervalResult(..), IntervalError(..), Input(..), InputContent(..), Environment(..), State(..),
                                                   Contract(..), Case(..), Payee(..), Action(..), TimeInterval(..), Observation(..), Value(..), ValueId,
                                                   Money, Party, POSIXTime(..), ivFrom, ivTo, inBounds, getAction, emptyState, getInputContent, Accounts, Token (Token))

-- EVALUATION

fixInterval :: TimeInterval -> State -> IntervalResult
fixInterval interval state = let
    TimeInterval low high  = interval
    curMinTime = minTime state
    -- newLow is both new "low" and new "minTime" (the lower bound for timeNum)
    newLow = max low curMinTime
    -- We know high is greater or equal than newLow (prove)
    curInterval = TimeInterval newLow high
    env = Environment { timeInterval = curInterval }
    newState = state { minTime = newLow }
    in if high < low then IntervalError (InvalidInterval interval)
    else if high < curMinTime then IntervalError (IntervalInPastError curMinTime interval)
    else IntervalTrimmed env newState


-- | Evaluate a @Value@ to Integer
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value = let
    eval = evalValue env state
    in case value of
        AvailableMoney accId token -> Map.findWithDefault 0 (accId, token) (accounts state)
        Constant integer     -> integer
        NegValue val         -> negate (eval val)
        AddValue lhs rhs     -> eval lhs + eval rhs
        SubValue lhs rhs     -> eval lhs - eval rhs
        MulValue lhs rhs     -> eval lhs * eval rhs
        DivValue lhs rhs     -> let n = eval lhs
                                    d = eval rhs
                                in if d == 0
                                   then 0
                                   else n `quot` d
        ChoiceValue choiceId ->
            Map.findWithDefault 0 choiceId (choices state)
        TimeIntervalStart    -> (getPOSIXTime . ivFrom . timeInterval) env
        TimeIntervalEnd      -> (getPOSIXTime . ivTo . timeInterval) env
        UseValue valId       -> Map.findWithDefault 0 valId (boundValues state)
        Cond cond thn els    -> if evalObservation env state cond then eval thn else eval els

-- | Evaluate an @Observation@ to Bool
evalObservation :: Environment -> State -> Observation -> Bool
evalObservation env state obs = let
    evalObs = evalObservation env state
    evalVal = evalValue env state
    in case obs of
        AndObs lhs rhs          -> evalObs lhs && evalObs rhs
        OrObs lhs rhs           -> evalObs lhs || evalObs rhs
        NotObs subObs           -> not (evalObs subObs)
        ChoseSomething choiceId -> choiceId `Map.member` choices state
        ValueGE lhs rhs         -> evalVal lhs >= evalVal rhs
        ValueGT lhs rhs         -> evalVal lhs > evalVal rhs
        ValueLT lhs rhs         -> evalVal lhs < evalVal rhs
        ValueLE lhs rhs         -> evalVal lhs <= evalVal rhs
        ValueEQ lhs rhs         -> evalVal lhs == evalVal rhs
        TrueObs                 -> True
        FalseObs                -> False


-- | Pick the first account with money in it
refundOne :: Accounts  -> Maybe ((Party, Token, Money), Accounts)
refundOne accounts = do
    (((accId, tok), balance), rest) <- Map.minViewWithKey accounts
    if balance > 0
    then Just ((accId, tok, balance), rest)
    else refundOne rest

data Payment = Payment Party Payee Token Money
  deriving (Eq,Ord,Show,Read)

data ReduceEffect = ReduceWithPayment Payment
                  | ReduceNoPayment
  deriving (Eq,Ord,Show,Read)


-- | Obtains the amount of money available an account
moneyInAccount :: Party -> Token -> Accounts -> Money
moneyInAccount accId token = Map.findWithDefault 0 (accId, token)


-- | Sets the amount of money available in an account
updateMoneyInAccount :: Party -> Token -> Money -> Accounts -> Accounts
updateMoneyInAccount accId token money =
    if money <= 0 then Map.delete (accId, token) else Map.insert (accId, token) money


{-| Add the given amount of money to an account (only if it is positive).
    Return the updated Map
-}
addMoneyToAccount :: Party -> Token -> Money -> Accounts -> Accounts
addMoneyToAccount accId token money accounts = let
    balance = moneyInAccount accId token accounts
    newBalance = balance + money
    in if money <= 0 then accounts
    else updateMoneyInAccount accId token newBalance accounts


{-| Gives the given amount of money to the given payee.
    Returns the appropriate effect and updated accounts
-}
giveMoney :: Party -> Payee -> Token -> Money -> Accounts -> (ReduceEffect, Accounts)
giveMoney accountId payee token amount accounts =
  let newAccounts = case payee of
                      Party _ -> accounts
                      Account accId -> addMoneyToAccount accId token amount accounts
  in (ReduceWithPayment (Payment accountId payee token amount), newAccounts)

-- REDUCE

data ReduceWarning = ReduceNoWarning
                   | ReduceNonPositivePay Party Payee Integer
                   | ReducePartialPay Party Payee Money Money
                                     -- ^ src    ^ dest ^ paid ^ expected
                   | ReduceShadowing ValueId Integer Integer
                                     -- oldVal ^  newVal ^

                   | ReduceAssertionFailed
  deriving (Eq,Ord,Show,Read)


data ReduceStepResult = Reduced ReduceWarning ReduceEffect State Contract
                      | NotReduced
                      | AmbiguousTimeIntervalReductionError
  deriving (Eq,Ord,Show,Read)


-- | Carry a step of the contract with no inputs
reduceContractStep :: Environment -> State -> Contract -> ReduceStepResult
reduceContractStep env state contract = case contract of

    Close -> case refundOne (accounts state) of
        Just ((party, token, money), newAccounts) -> let
            newState = state { accounts = newAccounts }
            in Reduced ReduceNoWarning (ReduceWithPayment (Payment party (Party party) token money)) newState Close
        Nothing -> NotReduced

    Pay accId payee token val cont -> let
        moneyToPay = evalValue env state val
        in  if moneyToPay <= 0
            then Reduced (ReduceNonPositivePay accId payee moneyToPay) ReduceNoPayment state cont
            else let
                balance    = moneyInAccount accId token (accounts state) -- always positive
                paidMoney  = min balance moneyToPay -- always positive
                newBalance = balance - paidMoney -- always positive
                newAccs    = updateMoneyInAccount accId token newBalance (accounts state)
                warning = if paidMoney < moneyToPay
                          then ReducePartialPay accId payee paidMoney moneyToPay
                          else ReduceNoWarning
                (payment, finalAccs) = giveMoney accId payee token paidMoney newAccs
                in Reduced warning payment (state { accounts = finalAccs }) cont

    If obs cont1 cont2 -> let
        cont = if evalObservation env state obs then cont1 else cont2
        in Reduced ReduceNoWarning ReduceNoPayment state cont

    When _ timeout cont -> let
        startTime = ivFrom (timeInterval env)
        endTime   = ivTo (timeInterval env)
        -- if timeout in future – do not reduce
        in if endTime < timeout then NotReduced
        -- if timeout in the past – reduce to timeout continuation
        else if timeout <= startTime then Reduced ReduceNoWarning ReduceNoPayment state cont
        -- if timeout in the time range – issue an ambiguity error
        else AmbiguousTimeIntervalReductionError

    Let valId val cont -> let
        evaluatedValue = evalValue env state val
        boundVals = boundValues state
        newState = state { boundValues = Map.insert valId evaluatedValue boundVals }
        warn = case Map.lookup valId boundVals of
              Just oldVal -> ReduceShadowing valId oldVal evaluatedValue
              Nothing     -> ReduceNoWarning
        in Reduced warn ReduceNoPayment newState cont

    Assert obs cont -> let
        warning = if evalObservation env state obs
                  then ReduceNoWarning
                  else ReduceAssertionFailed
        in Reduced warning ReduceNoPayment state cont

data ReduceResult = ContractQuiescent Bool [ReduceWarning] [Payment] State Contract
                  | RRAmbiguousTimeIntervalError
  deriving (Eq,Ord,Show,Read)

-- | Reduce a contract until it cannot be reduced more
reduceContractUntilQuiescent :: Environment -> State -> Contract -> ReduceResult
reduceContractUntilQuiescent env state contract = let
    reductionLoop
      :: Bool -> Environment -> State -> Contract -> [ReduceWarning] -> [Payment] -> ReduceResult
    reductionLoop reduced env state contract warnings payments =
        case reduceContractStep env state contract of
            Reduced warning effect newState cont -> let
                newWarnings = if warning == ReduceNoWarning then warnings
                              else warning : warnings
                newPayments  = case effect of
                    ReduceWithPayment payment -> payment : payments
                    ReduceNoPayment           -> payments
                in reductionLoop True env newState cont newWarnings newPayments
            AmbiguousTimeIntervalReductionError -> RRAmbiguousTimeIntervalError
            -- this is the last invocation of reductionLoop, so we can reverse lists
            NotReduced -> ContractQuiescent reduced (reverse warnings) (reverse payments) state contract

    in reductionLoop False env state contract [] []

data ApplyWarning = ApplyNoWarning
                  | ApplyNonPositiveDeposit Party Party Integer
  deriving (Eq,Ord,Show,Read)

data ApplyAction = AppliedAction ApplyWarning State
                 | NotAppliedAction
  deriving (Eq,Ord,Show,Read)

-- | Try to apply a single input contentent to a single action
applyAction :: Environment -> State -> InputContent -> Action -> ApplyAction
applyAction env state (IDeposit accId1 party1 token1 money) (Deposit accId2 party2 token2 val) =
    let amount = evalValue env state val
    in if accId1 == accId2 && party1 == party2 && token1 == token2 && money == amount
       then let warning = if amount > 0
                          then ApplyNoWarning
                          else ApplyNonPositiveDeposit party1 accId2 amount
                newState = state { accounts = addMoneyToAccount accId1 token1 money (accounts state) }
            in AppliedAction warning newState
       else NotAppliedAction
applyAction env state (IChoice choId1 choice) (Choice choId2 bounds) =
    if choId1 == choId2 && inBounds choice bounds
    then let newState = state { choices = Map.insert choId1 choice (choices state) }
         in AppliedAction ApplyNoWarning newState
    else NotAppliedAction
applyAction env state INotify (Notify obs) =
    if evalObservation env state obs
    then AppliedAction ApplyNoWarning state
    else NotAppliedAction
applyAction _ _ _ _ = NotAppliedAction

-- | Try to get a continuation from a pair of Input and Case
getContinuation :: Input -> Case -> Maybe Contract
getContinuation (NormalInput _) (Case _ continuation) = Just continuation
getContinuation (MerkleizedInput _ serialisedContinuation) (MerkleizedCase _ continuationHash) =
  if hash serialisedContinuation == continuationHash
  then case byteStringToContract serialisedContinuation of
        Nothing -> Nothing
        Just (c, bs) -> if BS.null bs then Just c else Nothing
  else Nothing
getContinuation _ _ = Nothing


data ApplyResult = Applied ApplyWarning State Contract
                 | ApplyNoMatchError
                 | ApplyHashMismatch
  deriving (Eq,Ord,Show,Read)

-- | Apply a single, potentially merkleized Input to the contract (assumes the contract is reduced)
applyCases :: Environment -> State -> Input -> [Case] -> ApplyResult
applyCases env state input (headCase : tailCase) =
  let inputContent = getInputContent input :: InputContent
      action = getAction headCase :: Action
      maybeContinuation = getContinuation input headCase :: Maybe Contract
  in
  case applyAction env state inputContent action of
    AppliedAction warning newState ->
      case maybeContinuation of
        Just continuation -> Applied warning newState continuation
        Nothing -> ApplyHashMismatch
    NotAppliedAction -> applyCases env state input tailCase

applyCases env state input [] = ApplyNoMatchError


applyInput :: Environment -> State -> Input -> Contract -> ApplyResult
applyInput env state input (When cases _ _) = applyCases env state input cases
applyInput _ _ _ _                          = ApplyNoMatchError

-- APPLY ALL

data TransactionWarning = TransactionNonPositiveDeposit Party Party Integer
                        | TransactionNonPositivePay Party Payee Integer
                        | TransactionPartialPay Party Payee Money Money
                                                -- ^ src    ^ dest ^ paid ^ expected
                        | TransactionShadowing ValueId Integer Integer
                                                -- oldVal ^  newVal ^
                        | TransactionAssertionFailed
  deriving (Eq,Ord,Show,Read)

convertReduceWarnings :: [ReduceWarning] -> [TransactionWarning]
convertReduceWarnings [] = []
convertReduceWarnings (first:rest) =
  (case first of
    ReduceNoWarning -> []
    ReduceNonPositivePay accId payee amount ->
            [TransactionNonPositivePay accId payee amount]
    ReducePartialPay accId payee paid expected ->
            [TransactionPartialPay accId payee paid expected]
    ReduceShadowing valId oldVal newVal ->
            [TransactionShadowing valId oldVal newVal]
    ReduceAssertionFailed ->
            [TransactionAssertionFailed])
  ++ convertReduceWarnings rest

convertApplyWarning :: ApplyWarning -> [TransactionWarning]
convertApplyWarning warn =
  case warn of
    ApplyNoWarning -> []
    ApplyNonPositiveDeposit party accId amount ->
            [TransactionNonPositiveDeposit party accId amount]

data ApplyAllResult = ApplyAllSuccess Bool [TransactionWarning] [Payment] State Contract
                    | ApplyAllHashMismatch
                    | ApplyAllNoMatchError
                    | ApplyAllAmbiguousTimeIntervalError
  deriving (Eq,Ord,Show)


-- | Apply a list of Inputs to the contract
applyAllInputs :: Environment -> State -> Contract -> [Input] -> ApplyAllResult
applyAllInputs env state contract inputs = let
    applyAllLoop
        :: Bool
        -> Environment
        -> State
        -> Contract
        -> [Input]
        -> [TransactionWarning]
        -> [Payment]
        -> ApplyAllResult
    applyAllLoop contractChanged env state contract inputs warnings payments =
        case reduceContractUntilQuiescent env state contract of
            RRAmbiguousTimeIntervalError -> ApplyAllAmbiguousTimeIntervalError
            ContractQuiescent reduced reduceWarns pays curState cont -> case inputs of
                [] -> ApplyAllSuccess (contractChanged || reduced)
                                      (warnings ++ convertReduceWarnings reduceWarns)
                                      (payments ++ pays) curState cont
                (input : rest) -> case applyInput env curState input cont of
                    Applied applyWarn newState cont ->
                        applyAllLoop True env newState cont rest
                                     (warnings ++ convertReduceWarnings reduceWarns
                                               ++ convertApplyWarning applyWarn)
                                     (payments ++ pays)
                    ApplyHashMismatch -> ApplyAllHashMismatch
                    ApplyNoMatchError -> ApplyAllNoMatchError
    in applyAllLoop False env state contract inputs [] []

data TransactionError = TEAmbiguousTimeIntervalError
                      | TEApplyHashMismatch
                      | TEApplyNoMatchError
                      | TEIntervalError IntervalError
                      | TEUselessTransaction
  deriving (Eq,Ord,Show,Read)

data TOR = TOR { txOutWarnings :: [TransactionWarning]
               , txOutPayments :: [Payment]
               , txOutState    :: State
               , txOutContract :: Contract }
  deriving (Eq,Ord,Show,Read)

data TransactionOutput =
    TransactionOutput TOR
  | Error TransactionError
  deriving (Eq,Ord,Show,Read)

data TransactionInput = TransactionInput
    { txInterval :: TimeInterval
    , txInputs   :: [Input] }
  deriving (Eq,Ord,Show,Read)

isClose :: Contract -> Bool
isClose Close = True
isClose _ = False

-- | Try to compute outputs of a transaction give its input
computeTransaction :: TransactionInput -> State -> Contract -> TransactionOutput
computeTransaction tx state contract = let
    inputs = txInputs tx
    in case fixInterval (txInterval tx) state of
        IntervalTrimmed env fixState -> case applyAllInputs env fixState contract inputs of
            ApplyAllSuccess reduced warnings payments newState cont -> let
                in  if not reduced && (not (isClose contract) || Map.null (accounts state))
                    then Error TEUselessTransaction
                    else TransactionOutput (TOR { txOutWarnings = warnings
                                                , txOutPayments = payments
                                                , txOutState = newState
                                                , txOutContract = cont })
            ApplyAllHashMismatch -> Error TEApplyHashMismatch
            ApplyAllNoMatchError -> Error TEApplyNoMatchError
            ApplyAllAmbiguousTimeIntervalError -> Error TEAmbiguousTimeIntervalError
        IntervalError error -> Error (TEIntervalError error)

playTraceAux :: TOR -> [TransactionInput] -> TransactionOutput
playTraceAux res [] = TransactionOutput res
playTraceAux TOR { txOutWarnings = warnings
                 , txOutPayments = payments
                 , txOutState = state
                 , txOutContract = cont } (h:t) =
  let transRes = computeTransaction h state cont in
  case transRes of
    TransactionOutput transResRec ->
      playTraceAux (transResRec { txOutPayments = payments ++ txOutPayments transResRec
                                , txOutWarnings = warnings ++ txOutWarnings transResRec})
                   t
    Error _ -> transRes

playTrace :: POSIXTime -> Contract -> [TransactionInput] -> TransactionOutput
playTrace sl c = playTraceAux (TOR { txOutWarnings = []
                                   , txOutPayments = []
                                   , txOutState = emptyState sl
                                   , txOutContract = c })

-- | Calculates an upper bound for the maximum lifespan of a contract
contractLifespanUpperBound :: Contract -> Integer
contractLifespanUpperBound contract = case contract of
    Close -> 0
    Pay _ _ _ _ cont -> contractLifespanUpperBound cont
    If _ contract1 contract2 ->
        max (contractLifespanUpperBound contract1) (contractLifespanUpperBound contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespanUpperBound cont) cases
        in maximum (getPOSIXTime timeout : contractLifespanUpperBound subContract : contractsLifespans)
    Let _ _ cont -> contractLifespanUpperBound cont
    Assert _ cont -> contractLifespanUpperBound cont


