{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Semantics
  ( tests
  )
  where

import qualified Arith
import Control.Monad.IO.Class (MonadIO (..))
import Data.Aeson (ToJSON (..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Core.Arbitrary
  ( arbitraryTimeIntervalAfter,
    arbitraryValidTransactions,
    genContract,
    genContract',
    genEnvironment,
    genState,
    genTransaction,
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
    reproducibleProperty',
  )
import Marlowe.Utils (showAsJson)
import Orderings (Ord (..))
import PositiveAccounts (validAndPositive_state)
import QuickCheck.GenT (suchThat, liftGen)
import Semantics
  ( TransactionOutput (..),
    TransactionOutputRecord_ext (TransactionOutputRecord_ext),
    TransactionWarning,
    Transaction_ext (..),
    computeTransaction,
    evalValue,
    evalObservation,
    isQuiescent,
    txOutWarnings,
    maxTimeContract,
  )
import SemanticsTypes
  ( Contract (..),
    State_ext (..),
    Value (..),
    minTime,
  )
import SingleInputTransactions (traceListToSingleInput)
import Test.QuickCheck (cover, withMaxSuccess)
import Test.QuickCheck.Monadic (assert, monitor, pre, run)
import Test.QuickCheck.Property (counterexample)
import Test.Tasty (TestTree, testGroup)
import Timeout (isClosedAndEmpty)
import TransactionBound (maxTransactionsInitialState)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Semantics"
    [ evalValueTest i
    , evalObservationTest i
    , divisionRoundsTowardsZeroTest i
    , computeTransactionTest i
    --
    -- Property based test correponding to theorems defined
    -- in Isabelle:
    --
    -- TransactionBound.thy
    , playTrace_only_accepts_maxTransactionsInitialStateTest i
    -- SingleInputTransactions.thy
    , traceToSingleInputIsEquivalentTest i
    -- QuiescentResults.thy
    , computeTransactionIsQuiescentTest i
    , playTraceIsQuiescentTest i
    -- Timeout.thy
    , timedOutTransaction_closes_contractTest i
    -- CloseIsSafe.thy
    , closeIsSafeTest i
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
          `suchThat` (\d -> (Arith.abs_int $ evalValue env state numerator) `Arith.less_int` (Arith.abs_int $ evalValue env state d))
        )
    let
        req :: Request JSON.Value
        req = EvalValue env state (DivValue numerator denominator)
        successResponse = RequestResponse $ toJSON (0 :: Int)
    assertResponse interpret req successResponse

computeTransactionTest :: InterpretJsonRequest -> TestTree
computeTransactionTest interpret = reproducibleProperty "Calling computeTransaction test" do
    contract <- run $ generateT $ genContract interpret `suchThat` (/=Close) -- arbitraryValidTransactions returns [] for the `Close` contract
    state <- run $ generateT $ genState interpret
    transactions <- run $ generate $ arbitraryValidTransactions state contract `suchThat` (not . null)

    let transaction = head transactions
        req :: Request JSON.Value
        req = ComputeTransaction transaction state contract

    RequestResponse res <- run $ liftIO $ interpret req
    case JSON.fromJSON res of
      JSON.Success transactionOutput  -> do
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
    all (flip elem l2) l1
    && all (flip elem l1) l2

-- TransactionBound.thy
--
-- lemma playTrace_only_accepts_maxTransactionsInitialState :
--    "playTrace sl c l = TransactionOutput txOut ⟹
--      length l ≤ maxTransactionsInitialState c"
playTrace_only_accepts_maxTransactionsInitialStateTest :: InterpretJsonRequest -> TestTree
playTrace_only_accepts_maxTransactionsInitialStateTest interpret = reproducibleProperty "Calling playTrace only accepts maxTransactionsInitialState"  do
    contract <- run $ generateT $ genContract interpret
    state <- run $ generateT $ genState interpret
    transactions <- run $ generate $ arbitraryValidTransactions state contract
    let
        req :: Request JSON.Value
        req = PlayTrace (Arith.integer_of_int $ minTime state) contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput TransactionOutputRecord_ext {}) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected maxTransactionsInitialState (" ++ show (maxTransactionsInitialState contract) ++ ")\n"
                ++ "to be an upper bound for the number of transacations (" ++ show (length transactions) ++ ")")
        assert $ toInteger (length transactions) <= Arith.integer_of_nat (maxTransactionsInitialState contract)
      JSON.Success (TransactionError _ ) -> pre False
      _ -> fail "JSON parsing failed!"

-- SingleInputTransactions.thy
--
-- theorem traceToSingleInputIsEquivalent:
--    "playTrace sn co tral = playTrace sn co (traceListToSingleInput tral)"
traceToSingleInputIsEquivalentTest :: InterpretJsonRequest -> TestTree
traceToSingleInputIsEquivalentTest interpret = reproducibleProperty "Single input transactions"  do
    (contractClass, contract, State_ext _ _ _ startTime _, transactions) <- run $ generateT $ (do
        (b,c) <- genContract' interpret `suchThat` (\(_,c) ->  Arith.integer_of_nat (maxTransactionsInitialState c) > 2)
        s <- genState interpret
        t <- liftGen $ arbitraryValidTransactions s c
        pure (b,c,s,t)) `suchThat` \(_,_,_,t) -> t /= traceListToSingleInput t

    let
        multipleInputs = PlayTrace (Arith.integer_of_int startTime) contract transactions
        singletonInput = PlayTrace (Arith.integer_of_int startTime) contract (traceListToSingleInput transactions)

    RequestResponse resMultipleInputs <- run $ liftIO $ interpret multipleInputs
    RequestResponse resSingletonInput <- run $ liftIO $ interpret singletonInput

    -- For more than half of the tests the contracts are expected to be arbitrary (i.e. not from golden contracts)
    pure $ cover 50.0 contractClass "arbitrary contracts" $ resMultipleInputs == resSingletonInput

-- QuiescentResults.thy
--
-- theorem computeTransactionIsQuiescent:
--    "validAndPositive_state sta ⟹
--      computeTransaction traIn sta cont = TransactionOutput traOut ⟹
--        isQuiescent (txOutContract traOut) (txOutState traOut)"
computeTransactionIsQuiescentTest :: InterpretJsonRequest -> TestTree
computeTransactionIsQuiescentTest interpret = reproducibleProperty "Calling computeTransaction is quiescent" do
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
                ++ "Expected reponse to be quiescent" )
        assert $ isQuiescent txOutContract txOutState
      _ -> fail "JSON parsing failed!"

-- QuiescentResults.thy
--
-- theorem playTraceIsQuiescent:
--    "playTrace sl cont (Cons h t) = TransactionOutput traOut ⟹
--      isQuiescent (txOutContract traOut) (txOutState traOut)"
playTraceIsQuiescentTest :: InterpretJsonRequest -> TestTree
playTraceIsQuiescentTest interpret = reproducibleProperty "Calling playTrace is quiescent" do
    contract <- run $ generateT $ genContract interpret `suchThat` (/=Close)
    state <- run $ generateT $ genState interpret
    transactions <- run $ generate $ arbitraryValidTransactions state contract `suchThat` (not . null)
    let
        req :: Request JSON.Value
        req = PlayTrace (Arith.integer_of_int $ minTime state) contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected reponse to be quiescent" )
        assert $ isQuiescent txOutContract txOutState
      JSON.Success _ -> pre False
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
timedOutTransaction_closes_contractTest interpret = reproducibleProperty "Timed-out transaction closes contract"  do
    (contract, state@(State_ext _ _ _ minTime' _)) <- run $ generateT $ do
      c <- genContract interpret `suchThat` (/=Close)
      s <- genState interpret `suchThat` validAndPositive_state
      pure (c,s) `suchThat` \(contract, State_ext accounts _ _ _ _) -> null accounts || contract /= Close
    interval <- run $ generate $ arbitraryTimeIntervalAfter minTime' `suchThat` \(iniTime, endTime) ->
           (iniTime `greater_eq` minTime')
        && (iniTime `greater_eq` maxTimeContract contract)
        && (endTime `greater_eq` iniTime)

    let transaction = Transaction_ext interval [] ()
        req :: Request JSON.Value
        req = ComputeTransaction transaction state contract

    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success txOut@(TransactionOutput trec) -> do
        let expected :: [TransactionWarning]
            expected = mempty
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected: " ++ show expected ++ "\n"
                ++ "Actual: " ++ show (txOutWarnings trec))
        assert $ isClosedAndEmpty txOut
      JSON.Success _ -> pre False
      _ -> fail "JSON parsing failed!"

-- CloseIsSafe.thy
--
-- theorem closeIsSafe :
--    "computeTransaction tra sta Close = TransactionOutput trec ⟹  txOutWarnings trec = []"
closeIsSafeTest :: InterpretJsonRequest -> TestTree
closeIsSafeTest interpret = reproducibleProperty "Close is safe" do
    state <- run $ generateT $ genState interpret
    transaction <- run $ generateT $ genTransaction interpret `suchThat` \(Transaction_ext (_,upper) _ _) -> minTime state `less_eq` upper
    let req :: Request JSON.Value
        req = ComputeTransaction transaction state Close

    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput trec) -> do
        let expected :: [TransactionWarning]
            expected = mempty
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected: " ++ show expected ++ "\n"
                ++ "Actual: " ++ show (txOutWarnings trec))
        assert (txOutWarnings trec == expected)
      JSON.Success _ -> pre False
      _ -> fail "JSON parsing failed!"
