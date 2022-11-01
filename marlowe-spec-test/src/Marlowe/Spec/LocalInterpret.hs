{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.LocalInterpret where

import Arith (Int(..))
import qualified Data.Aeson as JSON
import Test.Tasty (TestName)
import Test.Tasty.Providers (TestTree)
import Marlowe.Spec.Core.Serialization.Json (localJsonRoundtripSerialization)
import Test.Tasty.HUnit (testCase, (@?=))
import Marlowe.Spec.Interpret (Response(..), Request(..))
import Semantics (playTrace, computeTransaction)


interpretLocal :: Request JSON.Value -> Response JSON.Value
interpretLocal (TestRoundtripSerialization t v) =
  RequestResponse
    $ JSON.toJSON
    $ localJsonRoundtripSerialization t v
interpretLocal (PlayTrace t c is) =
  RequestResponse
    $ JSON.toJSON
    $ playTrace (Int_of_integer t) c is
interpretLocal (ComputeTransaction t s c) =
  RequestResponse
    $ JSON.toJSON
    $ computeTransaction t s c
interpretLocal _ = RequestNotImplemented

testLocal :: TestName -> Request JSON.Value -> Response JSON.Value -> TestTree
testLocal testName request expected = testCase testName
    (do
        interpretLocal request @?= expected
    )
