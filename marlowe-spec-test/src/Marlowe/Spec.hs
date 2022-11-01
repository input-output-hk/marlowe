{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec (tests) where

import Test.Tasty (TestTree, testGroup)
import Marlowe.Spec.Interpret (InterpretJsonRequest)
import qualified Marlowe.Spec.Core

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Marlowe"
  [ Marlowe.Spec.Core.tests i
  ]


