{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.Swap (tests) where

import Test.Tasty (TestTree, testGroup)
import Examples.Swap (swapExample, happyPathTransactions, happyPathPayments, unhappyPathPayments, unhappyPathTransactions)
import Marlowe.Spec.Core.Examples.Common (runScenario)
import Marlowe.Spec.Interpret (InterpretJsonRequest)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Swap"
    [ testHappyPath i
    , testUnhappyPath i
    ]

testHappyPath :: InterpretJsonRequest -> TestTree
testHappyPath =
  runScenario
    "Happy path"
    swapExample
    happyPathTransactions
    happyPathPayments

testUnhappyPath :: InterpretJsonRequest -> TestTree
testUnhappyPath =
  runScenario
    "Unhappy path"
    swapExample
    unhappyPathTransactions
    unhappyPathPayments
