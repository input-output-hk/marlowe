{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples.Escrow (tests) where

import Test.Tasty (TestTree, testGroup)
import Marlowe.Spec.Core.Examples.Common
import Marlowe.Spec.Interpret (InterpretJsonRequest)
import Examples.Escrow (confirmProblemPayments, dismissClaimPayments, confirmClaimPayments, escrowExample, confirmClaimTransactions, dismissClaimTransactions, confirmProblemTransactions, everythingIsAlrightPayments, everythingIsAlrightTransactions)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Escrow"
    [ everythingIsAlright i
    , confirmProblem i
    , dismissClaim i
    , confirmClaim i
    ]

everythingIsAlright :: InterpretJsonRequest -> TestTree
everythingIsAlright =
  runScenario
    "Everything is alright"
    escrowExample
    everythingIsAlrightTransactions
    everythingIsAlrightPayments

confirmProblem :: InterpretJsonRequest -> TestTree
confirmProblem =
  runScenario
    "Confirm Problem"
    escrowExample
    confirmProblemTransactions
    confirmProblemPayments

dismissClaim :: InterpretJsonRequest -> TestTree
dismissClaim =
  runScenario
    "Dismiss Claim"
    escrowExample
    dismissClaimTransactions
    dismissClaimPayments

confirmClaim :: InterpretJsonRequest -> TestTree
confirmClaim =
  runScenario
    "Confirm Claim"
    escrowExample
    confirmClaimTransactions
    confirmClaimPayments
