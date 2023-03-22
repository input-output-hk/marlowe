{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Semantics where

import Arith (less_int, abs_int)
import Data.Aeson (ToJSON(..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Core.Arbitrary (genValue, genState, genEnvironment, genObservation)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), Response (..))
import Marlowe.Spec.Reproducible (reproducibleProperty, reproducibleProperty', generate, generateT, assertResponse)
import Test.Tasty (TestTree, testGroup)
import Test.QuickCheck (withMaxSuccess)
import Test.QuickCheck.Monadic (run)
import Semantics (evalValue, evalObservation)
import SemanticsTypes (Value(..))
import QuickCheck.GenT (suchThat)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Semantics"
    [ evalValueTest i
    , evalObservationTest i
    , divisionRoundsTowardsZeroTest i
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

evalObservationTest :: InterpretJsonRequest -> TestTree
evalObservationTest interpret = reproducibleProperty "Eval Observation" do
    env <- run $ generate $ genEnvironment
    state <- run $ generateT $ genState interpret
    observation <- run $ generateT $ genObservation interpret
    let
        req :: Request JSON.Value
        req = EvalObservation env state observation
        successResponse = RequestResponse $ toJSON $ evalObservation env state observation
    assertResponse interpret req successResponse

divisionRoundsTowardsZeroTest :: InterpretJsonRequest -> TestTree
divisionRoundsTowardsZeroTest interpret = reproducibleProperty "Division rounding"  do
    env <- run $ generate $ genEnvironment
    state <- run $ generateT $ genState interpret
    numerator <- run $ generateT $ genValue interpret
    denominator <- run $ generateT
        (genValue interpret
          `suchThat` (\d -> (abs_int $ evalValue env state numerator) `less_int` (abs_int $ evalValue env state d))
        )
    let
        req :: Request JSON.Value
        req = EvalValue env state (DivValue numerator denominator)
        successResponse = RequestResponse $ toJSON (0 :: Int)
    assertResponse interpret req successResponse
