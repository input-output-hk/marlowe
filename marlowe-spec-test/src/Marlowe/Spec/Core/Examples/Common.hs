{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.Common (runScenario) where

import Marlowe.Spec.Core.Semantics (setEquals)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import SemanticsTypes (
  Contract (..),
  Payment (..),
  TransactionOutput (..),
  Transaction_ext (..),
  txOutContract,
  txOutPayments,
  txOutWarnings,
 )
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

runScenario :: String -> Contract -> [Transaction_ext ()] -> [Payment] -> InterpretJsonRequest -> TestTree
runScenario name contract transactions payments interpret =
  testCase
    name
    ( do
        res <- interpret $ PlayTrace 0 contract transactions
        case parseValidResponse res of
          Left err -> assertFailure err
          Right (TransactionError err) -> assertFailure $ "Transaction error: " ++ show err
          Right (TransactionOutput o) -> do
            txOutContract o @?= Close
            txOutWarnings o @?= []
            let msg = "Expected " <> show (txOutPayments o) <> " to contain the same elements as " <> show payments
            assertBool msg $ txOutPayments o `setEquals` payments
    )
