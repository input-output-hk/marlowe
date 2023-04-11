{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Semantics
  ( tests
  )
  where

import Arith
  ( Int (..),
    less_int,
    abs_int,
    integer_of_nat
  )
import AssetsPreservation (assetsInTransactions, assetsInState, assetsInExternalPayments)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Aeson (ToJSON (..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Core.Arbitrary
  ( arbitraryTransaction,
    arbitraryTimeIntervalAfter,
    arbitraryValidTransactions,
    genContract,
    genContract',
    genEnvironment,
    genState,
    genStateWithSize,
    genValue,
    genObservation,
    greater_eq
  )
import Marlowe.Spec.Interpret
  ( InterpretJsonRequest,
    Request (..),
    Response (..),
  )
import Marlowe.Spec.Reproducible
  ( assertResponse,
    generate,
    generateT,
    reproducibleProperty,
    reproducibleProperty', ReproducibleTest,
  )
import Marlowe.Utils (showAsJson)
import MultiAssets (plus_Assets, Assets, assetValue)
import Orderings (Ord (..))
import PositiveAccounts (validAndPositive_state)
import QuickCheck.GenT (frequency, suchThat, liftGen, GenT)
import Semantics
  ( TransactionOutput (..),
    TransactionOutputRecord_ext (TransactionOutputRecord_ext),
    Transaction_ext (..),
    computeTransaction,
    evalValue,
    evalObservation,
    isQuiescent,
    txOutWarnings,
    txOutPayments,
    maxTimeContract,
    inputs,
  )
import SemanticsTypes
  ( Contract (..),
    State_ext (..),
    Value (..), Token, Case (..), Action (..)
  )
import SingleInputTransactions (traceListToSingleInput)
import Test.QuickCheck (cover, withMaxSuccess)
import Test.QuickCheck.Monadic (assert, monitor, pre, run, stop, PropertyM)
import Test.QuickCheck.Property (counterexample)
import Test.Tasty (TestTree, testGroup)
import Timeout (isClosedAndEmpty)
import TransactionBound (maxTransactionsInitialState)
import Control.Monad (join)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Semantics" [ testSemantics i , testGuarantees i ]

testSemantics :: InterpretJsonRequest -> TestTree
testSemantics i = testGroup "Core"
    [ evalValueTest i
    , evalObservationTest i
    , divisionRoundsTowardsZeroTest i
    , computeTransactionTest i
    , computeTransactionForValidTransactionTest i
    ]

-- TODO: Move to its own file Guarantees.hs
-- Property based tests correponding to theorems defined in Isabelle.
testGuarantees :: InterpretJsonRequest -> TestTree
testGuarantees i = testGroup "Guarantees"
    [
    -- TransactionBound.thy
    -- TODO: Test skipped as it is currently taking too long
    -- playTrace_only_accepts_maxTransactionsInitialStateTest i
    -- SingleInputTransactions.thy
    -- TODO: Test skipped as it is currently taking too long
    -- , traceToSingleInputIsEquivalentTest i
    -- QuiescentResults.thy
    computeTransactionIsQuiescentTest i
    -- TODO: Test skipped as it is currently taking too long
    -- , playTraceIsQuiescentTest i
    -- Timeout.thy
    , timedOutTransaction_closes_contractTest i
    -- CloseIsSafe.thy
    , closeIsSafeTest i
    -- AssetsPreservation.thy
    , playTrace_preserves_assets i
    ]

-- The default maxSuccess is 100 and this tests modifies that to 500 as it was empirically found that 10 out of 10 times
-- an existing bug in the purescript implementation regarding division rounding was found. With the default 100 only
-- 5 out of 10 executions of the test found the problem.
-- As with all testing, the fact that the implementation passes this property-based test doesn't guarantee that there
-- are no bugs, only that the selected arbitrary examples didn't find one.
evalValueTest :: InterpretJsonRequest -> TestTree
evalValueTest interpret = reproducibleProperty' "Eval Value" (withMaxSuccess 500) do
    env <- run $ generate genEnvironment
    state <- run $ generateT $ genState interpret
    value <- run $ generateT $ genValue interpret
    let
        req :: Request JSON.Value
        req = EvalValue env state value
        successResponse = RequestResponse $ toJSON $ evalValue env state value
    assertResponse interpret req successResponse

evalObservationTest :: InterpretJsonRequest -> TestTree
evalObservationTest interpret = reproducibleProperty "Eval Observation" do
    env <- run $ generate genEnvironment
    state <- run $ generateT $ genState interpret
    observation <- run $ generateT $ genObservation interpret
    let
        req :: Request JSON.Value
        req = EvalObservation env state observation
        successResponse = RequestResponse $ toJSON $ evalObservation env state observation
    assertResponse interpret req successResponse

divisionRoundsTowardsZeroTest :: InterpretJsonRequest -> TestTree
divisionRoundsTowardsZeroTest interpret = reproducibleProperty "Division rounding"  do
    env <- run $ generate genEnvironment
    state <- run $ generateT $ genState interpret
    numerator <- run $ generateT $ genValue interpret
    denominator <- run $ generateT
        (genValue interpret
          `suchThat` (\d -> abs_int (evalValue env state numerator) `less_int` abs_int (evalValue env state d))
        )
    let
        req :: Request JSON.Value
        req = EvalValue env state (DivValue numerator denominator)
        successResponse = RequestResponse $ toJSON (0 :: Prelude.Int)
    assertResponse interpret req successResponse

computeTransactionTest :: InterpretJsonRequest -> TestTree
computeTransactionTest interpret = reproducibleProperty "Calling computeTransaction test" do
    contract <- run $ generateT $ genContract interpret
    state <- run $ generateT $ genState interpret
    transaction <- run $ generate $ arbitraryTransaction state contract
    checkComputeTransactionResult interpret contract state transaction

computeTransactionForValidTransactionTest :: InterpretJsonRequest -> TestTree
computeTransactionForValidTransactionTest interpret = reproducibleProperty "Calling computeTransaction (only valid transactions) test" do
    contract <- run $ generateT $ genContract interpret `suchThat` (/=Close) -- arbitraryValidTransactions returns [] for the `Close` contract
    state <- run $ generateT $ genState interpret
    transactions <- run $ generate $ arbitraryValidTransactions state contract `suchThat` (not . null)
    checkComputeTransactionResult interpret contract state (head transactions)

checkComputeTransactionResult :: MonadIO m => InterpretJsonRequest -> Contract -> State_ext () -> Transaction_ext () -> PropertyM m ()
checkComputeTransactionResult interpret contract state transaction = do
    let req :: Request JSON.Value
        req = ComputeTransaction transaction state contract

    RequestResponse res <- run $ liftIO $ interpret req
    case JSON.fromJSON res of
      JSON.Success transactionOutput -> do
        let expected = computeTransaction transaction state contract
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected: " ++ show expected ++ "\n"
                ++ "Actual: " ++ show transactionOutput)
        assert $ txOutEquals transactionOutput expected
      _ -> fail "JSON parsing failed!"

txOutEquals :: TransactionOutput -> TransactionOutput -> Bool
txOutEquals
  (TransactionOutput (TransactionOutputRecord_ext warnings1 payments1 (State_ext accounts1 choices1 boundValues1 minTime1 b1) contract1 a1))
  (TransactionOutput (TransactionOutputRecord_ext warnings2 payments2 (State_ext accounts2 choices2 boundValues2 minTime2 b2) contract2 a2)) =
    warnings1 == warnings2
    && setEquals payments1 payments2
    && setEquals (notZero accounts1) (notZero accounts2)
    && setEquals choices1 choices2
    && setEquals boundValues1 boundValues2
    && minTime1 == minTime2
    && contract1 == contract2
    && a1 == a2
    && b1 == b2
  where
    notZero = filter (\(_, i) -> less 0 i)
txOutEquals a b = a == b

setEquals :: Eq a => [a] -> [a] -> Bool
setEquals l1 l2 =
    all (`elem` l2) l1
    && all (`elem` l1) l2

-- TransactionBound.thy
--
-- lemma playTrace_only_accepts_maxTransactionsInitialState :
--    "playTrace sl c l = TransactionOutput txOut ⟹
--      length l ≤ maxTransactionsInitialState c"
-- TODO: Test skipped as it is currently taking too long
_playTrace_only_accepts_maxTransactionsInitialStateTest :: InterpretJsonRequest -> TestTree
_playTrace_only_accepts_maxTransactionsInitialStateTest interpret = reproducibleProperty "lemma playTrace_only_accepts_maxTransactionsInitialState"  do
    (contract, State_ext _ _ _ (Int_of_integer startTime) _, transactions) <- run $ generateT $
        frequency
          [ (5, genContractStateAndValidTransactions interpret)
          , (40, genContractStateAndValidTransactions interpret `suchThat` \(_,_,l) -> not (null l))
          , (55, genContractStateAndValidTransactions interpret `suchThat` \(_,_,l) -> length l > 1)
          ]
    let
        req :: Request JSON.Value
        req = PlayTrace startTime contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput TransactionOutputRecord_ext {}) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected maxTransactionsInitialState (" ++ show (maxTransactionsInitialState contract) ++ ")\n"
                ++ "to be an upper bound for the number of transactions (" ++ show (length transactions) ++ ")")
        stop $ cover 50.0 (length transactions > 1) "more than one transaction" $ toInteger (length transactions) <= integer_of_nat (maxTransactionsInitialState contract)
      JSON.Success (TransactionError _ ) -> pre False
      _ -> fail "JSON parsing failed!"

genContractStateAndValidTransactions :: InterpretJsonRequest -> GenT IO (Contract, State_ext (), [Transaction_ext ()])
genContractStateAndValidTransactions interpret = do
    c <- genContract interpret `suchThat` (/=Close)
    s <- genState interpret
    t <- liftGen $ arbitraryValidTransactions s c
    pure (c,s,t)

-- SingleInputTransactions.thy
--
-- theorem traceToSingleInputIsEquivalent:
--    "playTrace sn co tral = playTrace sn co (traceListToSingleInput tral)"
-- TODO: Test skipped as it is currently taking too long
_traceToSingleInputIsEquivalentTest :: InterpretJsonRequest -> TestTree
_traceToSingleInputIsEquivalentTest interpret = reproducibleProperty "theorem traceToSingleInputIsEquivalent"  do
    (contractClass, contract, State_ext _ _ _ (Int_of_integer startTime) _, transactions) <- run $ generateT $ (do
        (b,c) <- genContract' interpret `suchThat` (\(_,c) -> integer_of_nat (maxTransactionsInitialState c) > 2)
        s <- genState interpret
        t <- liftGen $ arbitraryValidTransactions s c
        pure (b,c,s,t)) `suchThat` \(_,_,_,t) -> t /= traceListToSingleInput t

    let
        multipleInputs = PlayTrace startTime contract transactions
        singletonInput = PlayTrace startTime contract (traceListToSingleInput transactions)

    RequestResponse resMultipleInputs <- run $ liftIO $ interpret multipleInputs
    RequestResponse resSingletonInput <- run $ liftIO $ interpret singletonInput

    case (JSON.fromJSON resMultipleInputs, JSON.fromJSON resSingletonInput) of
      (JSON.Success (TransactionOutput _), JSON.Success (TransactionOutput _)) ->

          -- For more than half of the tests the contracts are expected to be arbitrary (i.e. not from golden contracts)
          stop $ cover 50.0 contractClass "arbitrary contracts" $ resMultipleInputs == resSingletonInput

      (JSON.Success (TransactionError _), JSON.Success _) -> pre False
      (JSON.Success _ , JSON.Success (TransactionError _)) -> pre False
      _ -> fail "JSON parsing failed"

isWhen :: Contract -> Bool
isWhen (When _ _ _) = True
isWhen _ = False

-- QuiescentResults.thy
--
-- theorem computeTransactionIsQuiescent:
--    "validAndPositive_state sta ⟹
--      computeTransaction traIn sta cont = TransactionOutput traOut ⟹
--        isQuiescent (txOutContract traOut) (txOutState traOut)"
-- TODO: Improve test-data quality. Less than 10% of txinput are empty transaction, and manually checking I noticed a lot of timeouted contracts
computeTransactionIsQuiescentTest :: InterpretJsonRequest -> TestTree
computeTransactionIsQuiescentTest interpret = reproducibleProperty "theorem computeTransactionIsQuiescent" do
    contract <- run $ generateT $ genContract interpret `suchThat` (/=Close) -- arbitraryValidTransactions returns [] for the `Close` contract
    state <- run $ generateT $ genState interpret `suchThat` validAndPositive_state
    transactions <- run $ generate $ arbitraryValidTransactions state contract `suchThat` (not . null)
    let
        transaction = head transactions
        req :: Request JSON.Value
        req = ComputeTransaction transaction state contract

    RequestResponse res <- run $ liftIO $ interpret req
    case JSON.fromJSON res of
      JSON.Success (TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Response: " ++ showAsJson res ++ "\n"
                ++ "Expected reponse to be quiescent")
        stop $ cover 30.0 (length (inputs transaction) > 0) "Non empty transaction"
             $ cover 10.0 (isWhen txOutContract) "Output contract is a When statement"
             $ isQuiescent txOutContract txOutState
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err ) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"

-- QuiescentResults.thy
--
-- theorem playTraceIsQuiescent:
--    "playTrace sl cont (Cons h t) = TransactionOutput traOut ⟹
--      isQuiescent (txOutContract traOut) (txOutState traOut)"
-- TODO: Test skipped as it is currently taking too long. Not sure why, the data should be the same as for computeTransactionIsQuiescentTest
_playTraceIsQuiescentTest :: InterpretJsonRequest -> TestTree
_playTraceIsQuiescentTest interpret = reproducibleProperty "theorem playTraceIsQuiescent" do
    (contract, State_ext _ _ _ (Int_of_integer startTime) _, transactions) <- run $ generateT $
        frequency
          [ (45, genContractStateAndValidTransactions interpret `suchThat` \(_,_,l) -> not (null l))
          , (55, genContractStateAndValidTransactions interpret `suchThat` \(_,_,l) -> length l > 1)
          ]
    let
        req :: Request JSON.Value
        req = PlayTrace startTime contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Response: " ++ showAsJson res ++ "\n"
                ++ "Expected reponse to be quiescent" )
        assert $ isQuiescent txOutContract txOutState
      JSON.Success (TransactionError _ ) -> pre False
      _ -> fail "JSON parsing failed!"

-- Timeout.thy
--
-- theorem timedOutTransaction_closes_contract:
--    "validAndPositive_state sta
--       ⟹  iniTime ≥ minTime sta
--       ⟹  iniTime ≥ maxTimeContract cont
--       ⟹  endTime ≥ iniTime
--       ⟹  accounts sta ≠ [] ∨ cont ≠ Close
--       ⟹  isClosedAndEmpty (computeTransaction ⦇ interval = (iniTime, endTime), inputs = [] ⦈ sta cont)"
timedOutTransaction_closes_contractTest :: InterpretJsonRequest -> TestTree
timedOutTransaction_closes_contractTest interpret = reproducibleProperty "theorem timedOutTransaction_closes_contract"  do
    (contract, state@(State_ext _ _ _ minTime' _)) <- run $ generateT $ (do
      c <- genContract interpret
      s <- genState interpret `suchThat` validAndPositive_state
      pure (c,s)) `suchThat` \(contract, State_ext accounts _ _ _ _) -> not (null accounts) || contract /= Close
    interval <- run $ generate $ arbitraryTimeIntervalAfter minTime' `suchThat` \(iniTime, endTime) ->
           (iniTime `greater_eq` minTime')
        && (iniTime `greater_eq` maxTimeContract contract)
        && (endTime `greater_eq` iniTime)

    let transaction = Transaction_ext interval [] ()
        req :: Request JSON.Value
        req = ComputeTransaction transaction state contract

    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success txOut@(TransactionOutput (TransactionOutputRecord_ext _ txOutPayment txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "txOutContract: " ++ show txOutContract
                ++ "txOutState: " ++ show txOutState)
        stop $ cover 100.0 (length (inputs transaction) == 0) "Transaction without inputs"
             $ cover 10.0 (length txOutPayment > 1) "Timeout contract produces payments"
             $ cover 70.0 (integer_of_nat (maxTransactionsInitialState contract) >= 1) "At least 1 transaction"
             $ cover 10.0 (integer_of_nat (maxTransactionsInitialState contract) >= 3) "At least 3 transactions"
             $ isClosedAndEmpty txOut
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err ) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"

-- CloseIsSafe.thy
--
-- theorem closeIsSafe :
--    "computeTransaction tra sta Close = TransactionOutput trec ⟹  txOutWarnings trec = []"
closeIsSafeTest :: InterpretJsonRequest -> TestTree
closeIsSafeTest interpret = reproducibleProperty "theorem closeIsSafe" do
    -- NOTE: To satisfy the premise that computeTransaction on a Close results in a succesful TransactionOutput
    --       we need for the state to have at least one account (Which we guarantee by using the state with size generator)
    --       This is also shown by the cover test below, which show that all valid transactions necesarly are the empty transaction
    --       and that it always produce payments. If the accounts were empty then an empty transaction would yield
    --       the error Useless Transaction, and moreover, there isn't a valid transaction possible
    --       TODO: Make lemmas about these last two observations.
    state@(State_ext _ _ _ startTime _) <- run $ generateT $ genStateWithSize ((1, 4), (0, 4), (0, 4)) interpret

    transaction <-  run $ generate $ arbitraryTransaction state Close `suchThat` \(Transaction_ext (_,upper) _ _) -> startTime `less_eq` upper
    let req :: Request JSON.Value
        req = ComputeTransaction transaction state Close

    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput trec) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected: no warnings\n"
                ++ "Actual: " ++ show (txOutWarnings trec))
        stop $ cover 100.0 (length (inputs transaction) == 0) "Transaction without inputs"
             $ cover 100.0 (length (txOutPayments trec) > 0) "Close contract produces payments"
             $ length (txOutWarnings trec) == 0
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err ) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"

-- AssetsPreservation.thy
--
-- theorem playTrace_preserves_assets :
--   assumes "playTrace slot contract txs = TransactionOutput out"
--     shows "assetsInTransactions txs
--          = assetsInState (txOutState out) + assetsInExternalPayments (txOutPayments out)"
playTrace_preserves_assets :: InterpretJsonRequest -> TestTree
playTrace_preserves_assets interpret = reproducibleProperty "Calling playTrace is quiescent" do
    (contract, State_ext _ _ _ (Int_of_integer startTime) _, transactions) <- run $ generateT $
        frequency
          [ (5, genContractStateAndValidTransactions interpret)
          , (45, genContractStateAndValidTransactions interpret `suchThat` \(_,_,l) -> not (null l))
          , (50, genContractStateAndValidTransactions interpret `suchThat` \(_,_,l) -> length l > 1)
          ]
    let
        req :: Request JSON.Value
        req = PlayTrace startTime contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput (TransactionOutputRecord_ext _ txOutPayments txOutState _ _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Response: " ++ showAsJson res ++ "\n"
                ++ "Expected reponse to be quiescent" )
        assert $ equals_Assets
          (assetsInTransactions transactions)
          (assetsInState txOutState `plus_Assets` assetsInExternalPayments txOutPayments)
          (tokensInContract contract)
      JSON.Success (TransactionError _ ) -> pre False
      _ -> fail "JSON parsing failed!"

  where
    -- TODO: export the function from Isabelle
    equals_Assets :: Assets -> Assets -> [Token] -> Bool
    equals_Assets assets1 assets2 = foldl (&&) True .
      map (\tok -> integer_of_nat (assetValue tok assets1) == integer_of_nat (assetValue tok assets2))

    tokensInContract :: Contract -> [Token]
    tokensInContract Close = []
    tokensInContract (Pay _ _ token _ cont) = token : tokensInContract cont
    tokensInContract (If _ cont1 cont2) = tokensInContract cont1 ++ tokensInContract cont2
    tokensInContract (When cases _ cont) = tokensInContract cont ++ join (map tokensInCases cases)
    tokensInContract (Let _ _ cont) = tokensInContract cont
    tokensInContract (Assert _ cont) = tokensInContract cont

    tokensInCases :: Case -> [Token]
    tokensInCases (Case (Deposit _ _ token _) cont) = token : tokensInContract cont
    tokensInCases (Case (Choice _ _ ) cont) = tokensInContract cont
    tokensInCases (Case (Notify _ ) cont) = tokensInContract cont
