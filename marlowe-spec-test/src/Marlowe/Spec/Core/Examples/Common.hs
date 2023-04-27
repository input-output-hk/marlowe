{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.Common (runScenario) where

import Test.Tasty (TestTree)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import SemanticsTypes (Contract(..), TransactionOutput(..), txOutContract, txOutWarnings, txOutPayments, Transaction_ext (..), Payment (..))

runScenario :: String -> Contract -> [Transaction_ext ()] -> [Payment] -> InterpretJsonRequest -> TestTree
runScenario name contract transactions payments interpret = testCase name
    ( do
        res <- interpret $ PlayTrace 0 contract transactions
        case parseValidResponse res of
            Left err -> assertFailure err
            Right (TransactionError err) -> assertFailure $ "Transaction error: " ++ show err
            Right (TransactionOutput o) -> do
              txOutContract o @?= Close
              txOutWarnings o @?= []
              txOutPayments o @?= payments
    )
