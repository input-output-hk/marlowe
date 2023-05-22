{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.ContractForDifference (tests) where

import Test.Tasty (TestTree, testGroup)
import Marlowe.Spec.Core.Examples.Common
import Marlowe.Spec.Interpret (InterpretJsonRequest)
import Examples.ContractForDifference

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "ContractForDifference"
  [ simpleScenario i
  ]

simpleScenario :: InterpretJsonRequest -> TestTree
simpleScenario =
  runScenario
    "Simple scenario"
    cfdExample
    cfdExampleTransactions
    cfdExamplePayments
