{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core (tests) where

import Test.Tasty (TestTree, testGroup)
import qualified Marlowe.Spec.Core.Examples
import qualified Marlowe.Spec.Core.Serialization.Json
import qualified Marlowe.Spec.Core.Semantics
import qualified Marlowe.Spec.Core.Guarantees
import Marlowe.Spec.Interpret (InterpretJsonRequest)

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Core"
  [ Marlowe.Spec.Core.Serialization.Json.tests i
  , Marlowe.Spec.Core.Semantics.tests i
  , Marlowe.Spec.Core.Guarantees.tests i
  , Marlowe.Spec.Core.Examples.tests i
  ]
