{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Semantics where
import Test.Tasty (TestTree, testGroup)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), Response (..))
import Test.QuickCheck.Monadic (run)
import Marlowe.Spec.Core.Arbitrary (genValue, genState, genEnvironment)
import Semantics (evalValue)
import Data.Aeson (ToJSON(..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Reproducible (reproducibleProperty', generate, generateT, assertResponse)
import Test.QuickCheck (withMaxSuccess)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Semantics"
    [ evalValueTest i
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


