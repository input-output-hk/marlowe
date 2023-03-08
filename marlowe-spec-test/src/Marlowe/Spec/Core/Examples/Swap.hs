{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.Swap (tests) where

import Test.Tasty (TestTree, testGroup)
import Examples.Swap (swapExample, successfulExecutionPathTransactions, successfulExecutionPathPayments, partialExecutionPathPayments, partialExecutionPathTransactions)
import Marlowe.Spec.Core.Examples.Common (runScenario)
import Marlowe.Spec.Interpret (InterpretJsonRequest)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Swap"
    [ testsuccessfulExecutionPath i
    , testpartialExecutionPath i
    ]

testsuccessfulExecutionPath :: InterpretJsonRequest -> TestTree
testsuccessfulExecutionPath =
  runScenario
    "Successful execution"
    swapExample
    successfulExecutionPathTransactions
    successfulExecutionPathPayments

testpartialExecutionPath :: InterpretJsonRequest -> TestTree
testpartialExecutionPath =
  runScenario
    "Partial execution"
    swapExample
    partialExecutionPathTransactions
    partialExecutionPathPayments
