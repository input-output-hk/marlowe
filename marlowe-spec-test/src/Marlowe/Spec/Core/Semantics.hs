{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Semantics where

import qualified Arith as Arith
import Data.Aeson (ToJSON(..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Core.Arbitrary (genValue, genState, genEnvironment, genContract, genTransaction, arbitraryNonnegativeInteger)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), Response (..))
import Marlowe.Spec.Reproducible (reproducibleProperty, reproducibleProperty', generate, generateT, assertResponse)
import Test.Tasty (TestTree, testGroup)
import Test.QuickCheck (withMaxSuccess)
import Test.QuickCheck.Monadic (assert, run)
import Semantics (evalValue, playTrace)
import SemanticsTypes (Value(..))
import SingleInputTransactions (traceListToSingleInput)
import QuickCheck.GenT (suchThat)
import QuickCheck.GenT (listOf)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Semantics"
    [ evalValueTest i
    , divisionRoundsTowardsZeroTest i
    , singleInput i
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
singleInput :: InterpretJsonRequest -> TestTree
singleInput interpret = reproducibleProperty "Single input"  do
    contract <- run $ generateT $ genContract interpret
    transactions <- run $ generateT $ listOf $ genTransaction interpret
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
