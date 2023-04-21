{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.Swap (tests) where
import Test.Tasty (TestTree, testGroup)
import qualified Examples.Swap
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import SemanticsTypes (Contract(..), TransactionOutput(..), txOutContract, txOutWarnings, txOutPayments)


tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Swap"
    [ testHappyPath i
    ]

testHappyPath :: InterpretJsonRequest -> TestTree
testHappyPath interpret = testCase "Happy path"
    ( do
        res <- interpret $ PlayTrace 0 Examples.Swap.swapExample Examples.Swap.happyPathTransactions
        case parseValidResponse res of
            Left err -> assertFailure err
            Right (TransactionError err) -> assertFailure $ "Transaction error: " ++ show err
            Right (TransactionOutput o) -> do
              txOutContract o @?= Close
              txOutWarnings o @?= []
              txOutPayments o @?= Examples.Swap.happyPathPayments
    )
