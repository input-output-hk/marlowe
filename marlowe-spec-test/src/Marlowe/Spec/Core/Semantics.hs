{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Semantics where

import qualified Arith as Arith
import Control.Monad.IO.Class (MonadIO(..))
import Data.Aeson (ToJSON(..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Core.Arbitrary (genValue, genState, genEnvironment, genContract, genTransaction, arbitraryNonnegativeInteger)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), Response (..))
import Marlowe.Spec.Reproducible (reproducibleProperty, reproducibleProperty', generate, generateT, assertResponse)
import Test.Tasty (TestTree, testGroup)
import Test.QuickCheck (withMaxSuccess)
import Test.QuickCheck.Monadic (assert, run, monitor)
import Semantics (evalValue, playTrace, computeTransaction, TransactionOutput (..), TransactionOutputRecord_ext (TransactionOutputRecord_ext), isQuiescent)
import SemanticsTypes (Value(..), State_ext (..))
import SingleInputTransactions (traceListToSingleInput)
import QuickCheck.GenT (suchThat)
import QuickCheck.GenT (listOf)
import Test.QuickCheck.Property (counterexample)
import Marlowe.Utils (showAsJson)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Semantics"
    [ evalValueTest i
    , divisionRoundsTowardsZeroTest i
    , traceToSingleInputIsEquivalent i
    , computeTransactionIsQuiescent i
    ]

-- The default maxSuccess is 100 and this tests modifies that to 500 as it was empirically found that 10 out of 10 times
-- an existing bug in the purescript implementation regarding division rounding was found. With the default 100 only
-- 5 out of 10 executions of the test found the problem.
-- As with all testing, the fact that the implementation passes this property-based test doesn't guarantee that there
-- are no bugs, only that the selected arbitrary examples didn't find one.
evalValueTest :: InterpretJsonRequest -> TestTree
evalValueTest interpret = reproducibleProperty' "Eval Value" (withMaxSuccess 500) do
    env <- run $ generate $ genEnvironment
    state <- run $ generateT $ genState interpret
    value <- run $ generateT $ genValue interpret
    let
        req :: Request JSON.Value
        req = EvalValue env state value
        successResponse = RequestResponse $ toJSON $ evalValue env state value
    assertResponse interpret req successResponse

divisionRoundsTowardsZeroTest :: InterpretJsonRequest -> TestTree
divisionRoundsTowardsZeroTest interpret = reproducibleProperty "Division rounding"  do
    env <- run $ generate $ genEnvironment
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

-- theorem traceToSingleInputIsEquivalent:
--    "playTrace sn co tral = playTrace sn co (traceListToSingleInput tral)"
traceToSingleInputIsEquivalent :: InterpretJsonRequest -> TestTree
traceToSingleInputIsEquivalent interpret = reproducibleProperty "Single input transactions"  do
    contract <- run $ generateT $ genContract interpret
    transactions <- run $ generateT $ (listOf $ genTransaction interpret) `suchThat` \t -> t /= traceListToSingleInput t
    startTime <- run $ generate $ arbitraryNonnegativeInteger

    let
        multipleInputs = PlayTrace (integer_of_int startTime) contract transactions
        singletonInput = PlayTrace (integer_of_int startTime) contract (traceListToSingleInput transactions)

        multipleInputsResponse = RequestResponse $ toJSON $ playTrace startTime contract transactions
        singletonInputResponse = RequestResponse $ toJSON $ playTrace startTime contract (traceListToSingleInput transactions)

    assertResponse interpret multipleInputs multipleInputsResponse
    assertResponse interpret singletonInput singletonInputResponse

    assert $ multipleInputsResponse == singletonInputResponse

integer_of_int :: Arith.Int -> Integer
integer_of_int (Arith.Int_of_integer k) = k

-- QuiescentResults.thy
-- theorem computeTransactionIsQuiescent:
--    "validAndPositive_state sta ⟹
--      computeTransaction traIn sta cont = TransactionOutput traOut ⟹
--        isQuiescent (txOutContract traOut) (txOutState traOut)"
computeTransactionIsQuiescent :: InterpretJsonRequest -> TestTree
computeTransactionIsQuiescent interpret = reproducibleProperty "Compute transaction is quiescent" do
    contract <- run $ generateT $ genContract interpret
    state <- run $ generateT $ genState interpret
    transactions <- run $ generateT $ genTransaction interpret
    let
        req :: Request JSON.Value
        req = ComputeTransaction transactions state contract
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success transactionOutput  -> do
        let expected = computeTransaction transactions state contract
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected: " ++ show expected ++ "\n"
                ++ "Actual: " ++ show transactionOutput)
        assert $ equals transactionOutput expected
      _ -> fail "JSON parsing failed!"

  where
    equals :: TransactionOutput -> TransactionOutput -> Bool
    equals
      (TransactionOutput (TransactionOutputRecord_ext warnings1 payments1 (State_ext accounts1 choices1 boundValues1 minTime1 b1) contract1 a1))
      (TransactionOutput (TransactionOutputRecord_ext warnings2 payments2 (State_ext accounts2 choices2 boundValues2 minTime2 b2) contract2 a2)) =
        warnings1 == warnings2
        && payments1 == payments2
        && accounts1 == accounts2
        && setEquals choices1 choices2
        && setEquals boundValues1 boundValues2
        && minTime1 == minTime2
        && contract1 == contract2
        && a1 == a2
        && b1 == b2
    equals a b = a == b

    setEquals :: Eq a => [a] -> [a] -> Bool
    setEquals l1 l2 =
        all (flip elem l2) l1
        && all (flip elem l1) l2

-- QuiescentResults.thy
-- theorem playTraceIsQuiescent:
--    "playTrace sl cont (Cons h t) = TransactionOutput traOut ⟹
--      isQuiescent (txOutContract traOut) (txOutState traOut)"
playTraceIsQuiescent :: InterpretJsonRequest -> TestTree
playTraceIsQuiescent interpret = reproducibleProperty "Play trace is quiescent" do
    contract <- run $ generateT $ genContract interpret
    transactions <- run $ generateT $ listOf $ genTransaction interpret
    startTime <- run $ generate $ arbitraryNonnegativeInteger
    let
        req :: Request JSON.Value
        req = PlayTrace (integer_of_int startTime) contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected reponse to be quiescent" )
        assert $ isQuiescent txOutContract txOutState
      _ -> fail "JSON parsing failed!"
