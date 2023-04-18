{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Semantics
  ( tests
  )
  where

import Arith
  ( abs_int,
    less_int,
  )
import Control.Monad.IO.Class (MonadIO (..))
import Data.Aeson (ToJSON (..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Core.Arbitrary (genEnvironment)
import Marlowe.Spec.Core.Guarantees
  ( SemiArbitrary (..),
    arbitraryTransaction,
    arbitraryValidTransactions,
    genContext
  )
import Marlowe.Spec.Interpret
  ( InterpretJsonRequest,
    Request (..),
    Response (..)
  )
import Marlowe.Spec.Reproducible
  ( assertResponse,
    generate,
    generateT,
    reproducibleProperty,
    reproducibleProperty'
  )
import Marlowe.Utils (showAsJson)
import Orderings (Ord (..))
import QuickCheck.GenT (suchThat)
import Semantics
  ( TransactionOutput (..),
    TransactionOutputRecord_ext (..),
    Transaction_ext (..),
    computeTransaction,
    evalObservation,
    evalValue
  )
import SemanticsTypes
  ( Contract (..),
    State_ext (..),
    Value (..)
  )
import Test.QuickCheck (withMaxSuccess)
import Test.QuickCheck.Monadic (PropertyM, assert, monitor, run)
import Test.QuickCheck.Property (counterexample)
import Test.Tasty (TestTree, testGroup)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Semantics"
    [ evalValueTest i
    , evalObservationTest i
    , divisionRoundsTowardsZeroTest i
    , computeTransactionTest i
    , computeTransactionForValidTransactionTest i
    ]

-- The default maxSuccess is 100 and this tests modifies that to 500 as it was empirically found that 10 out of 10 times
-- an existing bug in the purescript implementation regarding division rounding was found. With the default 100 only
-- 5 out of 10 executions of the test found the problem.
-- As with all testing, the fact that the implementation passes this property-based test doesn't guarantee that there
-- are no bugs, only that the selected arbitrary examples didn't find one.
evalValueTest :: InterpretJsonRequest -> TestTree
evalValueTest interpret = reproducibleProperty' "Eval Value" (withMaxSuccess 500) do
    context <- run $ generateT $ genContext interpret
    env <- run $ generate genEnvironment
    state <- run $ generate $ semiArbitrary context
    value <- run $ generate $ semiArbitrary context
    let
        req :: Request JSON.Value
        req = EvalValue env state value
        successResponse = RequestResponse $ toJSON $ evalValue env state value
    assertResponse interpret req successResponse

evalObservationTest :: InterpretJsonRequest -> TestTree
evalObservationTest interpret = reproducibleProperty "Eval Observation" do
    context <- run $ generateT $ genContext interpret
    env <- run $ generate genEnvironment
    state <- run $ generate $ semiArbitrary context
    observation <- run $ generate $ semiArbitrary context
    let
        req :: Request JSON.Value
        req = EvalObservation env state observation
        successResponse = RequestResponse $ toJSON $ evalObservation env state observation
    assertResponse interpret req successResponse

divisionRoundsTowardsZeroTest :: InterpretJsonRequest -> TestTree
divisionRoundsTowardsZeroTest interpret = reproducibleProperty "Division rounding"  do
    context <- run $ generateT $ genContext interpret
    env <- run $ generate genEnvironment
    state <- run $ generate $ semiArbitrary context
    numerator <- run $ generate $ semiArbitrary context
    denominator <- run $ generate
        (semiArbitrary context
          `suchThat` (\d -> abs_int (evalValue env state numerator) `less_int` abs_int (evalValue env state d))
        )
    let
        req :: Request JSON.Value
        req = EvalValue env state (DivValue numerator denominator)
        successResponse = RequestResponse $ toJSON (0 :: Prelude.Int)
    assertResponse interpret req successResponse

computeTransactionTest :: InterpretJsonRequest -> TestTree
computeTransactionTest interpret = reproducibleProperty "Calling computeTransaction test" do
    context <- run $ generateT $ genContext interpret
    contract <- run $ generate $ semiArbitrary context
    state <- run $ generate $ semiArbitrary context
    transaction <- run $ generate $ arbitraryTransaction state contract
    checkComputeTransactionResult interpret contract state transaction

computeTransactionForValidTransactionTest :: InterpretJsonRequest -> TestTree
computeTransactionForValidTransactionTest interpret = reproducibleProperty "Calling computeTransaction (only valid transactions) test" do
    context <- run $ generateT $ genContext interpret
    contract <- run $ generate $ semiArbitrary context `suchThat` (/=Close) -- arbitraryValidTransactions returns [] for the `Close` contract
    state <- run $ generate $ semiArbitrary context
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
