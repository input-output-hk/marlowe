{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Examples (tests) where
import Test.Tasty (TestTree, testGroup)
import qualified Marlowe.Spec.Core.Examples.ContractForDifference
import qualified Marlowe.Spec.Core.Examples.Escrow
import qualified Marlowe.Spec.Core.Examples.Swap
import Marlowe.Spec.Interpret (InterpretJsonRequest)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Contract examples"
  [ Marlowe.Spec.Core.Examples.Swap.tests i
  , Marlowe.Spec.Core.Examples.Escrow.tests i
  , Marlowe.Spec.Core.Examples.ContractForDifference.tests i
  ]
