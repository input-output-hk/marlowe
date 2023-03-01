{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.Escrow (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import Semantics (TransactionOutput(..), txOutContract, txOutWarnings, txOutPayments, Transaction_ext (..), Payment (..))
import SemanticsTypes (Contract(..))
import Examples.Escrow (confirmProblemPayments, dismissClaimPayments, confirmClaimPayments, escrowExample, confirmClaimTransactions, dismissClaimTransactions, confirmProblemTransactions, everythingIsAlrightPayments, everythingIsAlrightTransactions)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Escrow"
    [ everythingIsAlright i
    , confirmProblem i
    , dismissClaim i
    , confirmClaim i
    ]

everythingIsAlright :: InterpretJsonRequest -> TestTree
everythingIsAlright = runScenario "Everything is alright" everythingIsAlrightTransactions everythingIsAlrightPayments

confirmProblem :: InterpretJsonRequest -> TestTree
confirmProblem = runScenario "Confirm Problem" confirmProblemTransactions confirmProblemPayments

dismissClaim :: InterpretJsonRequest -> TestTree
dismissClaim = runScenario "Dismiss Claim" dismissClaimTransactions dismissClaimPayments

confirmClaim :: InterpretJsonRequest -> TestTree
confirmClaim = runScenario "Confirm Claim" confirmClaimTransactions confirmClaimPayments

runScenario :: String -> [Transaction_ext ()] -> [Payment] -> InterpretJsonRequest -> TestTree
runScenario name transactions payments interpret = testCase name
    ( do
        res <- interpret $ PlayTrace 0 escrowExample transactions
        case parseValidResponse res of
            Left err -> assertFailure err
            Right (TransactionError err) -> assertFailure $ "Transaction error: " ++ show err
            Right (TransactionOutput o) -> do
              txOutContract o @?= Close
              txOutWarnings o @?= []
              txOutPayments o @?= payments
    )
