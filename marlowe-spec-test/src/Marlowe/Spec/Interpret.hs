{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module Marlowe.Spec.Interpret
  ( Request(..)
  , Response(..)
  , InterpretJsonRequest
  , parseValidResponse
  , exactMatch
  , testResponse
  ) where

import qualified SemanticsTypes as C
import qualified Semantics as C
import Control.Applicative ((<|>))
import Data.Aeson (object, (.=), (.:), Result (..), fromJSON)
import Data.Aeson.Types (ToJSON(..), FromJSON(..))
import qualified Data.Aeson.Types as JSON
import Marlowe.Spec.TypeId (TypeId (..))
import Test.Tasty (TestName)
import Test.Tasty.Providers (TestTree)
import Test.Tasty.HUnit (testCase, (@?=), Assertion)
import MarloweCoreJson()

data Request transport
  = TestRoundtripSerialization TypeId transport
  | GenerateRandomValue TypeId
  | ComputeTransaction (C.Transaction_ext ()) (C.State_ext ()) C.Contract
  | PlayTrace Integer C.Contract [C.Transaction_ext ()]

instance ToJSON (Request JSON.Value) where
  toJSON (TestRoundtripSerialization t v) = object
    [ "request" .= JSON.String "test-roundtrip-serialization"
    , "typeId" .= toJSON t
    , "json"  .= v
    ]
  toJSON (GenerateRandomValue t) = object
    [ "request" .= JSON.String "generate-random-value"
    , "typeId" .= toJSON t
    ]
  toJSON (ComputeTransaction i s c) = object
    [ "request" .= JSON.String "compute-transaction"
    , "transactionInput" .= toJSON i
    , "coreContract" .= toJSON c
    , "state" .= toJSON s
    ]
  toJSON (PlayTrace t c is) = object
    [ "request" .= JSON.String "playtrace"
    , "transactionInputs" .= toJSON is
    , "coreContract" .= toJSON c
    , "initialTime" .= toJSON t
    ]


data Response transport
  = InvalidRequest String
  | UnknownRequest
  | RequestResponse transport
  | RequestNotImplemented
    deriving (Show, Eq)

instance FromJSON (Response JSON.Value) where
    parseJSON (JSON.String "UnknownRequest") = return UnknownRequest
    parseJSON (JSON.String "RequestNotImplemented") = return RequestNotImplemented
    parseJSON (JSON.Object v) = asError <|> asSuccess
        where
        asError = InvalidRequest <$> v .: "invalid-request"
        asSuccess = RequestResponse <$> v .: "request-response"
    parseJSON _ = fail "Response must be either a string or an object"


parseValidResponse :: FromJSON a => Response JSON.Value -> Either String a
parseValidResponse (InvalidRequest err) = Left $ "Invalid request: " ++ err
parseValidResponse UnknownRequest = Left $ "Unknown request"
parseValidResponse RequestNotImplemented = Left $ "Request not implemented"
parseValidResponse (RequestResponse v) = case fromJSON v of
  (Error err) -> Left $ "Invalid response: " ++ err
  (Success a) -> Right a

type InterpretJsonRequest = Request JSON.Value -> IO (Response JSON.Value)

testResponse :: InterpretJsonRequest -> TestName -> Request JSON.Value -> (Response JSON.Value -> Assertion) -> TestTree
testResponse interpret testName req assertion =
  testCase testName $ assertion =<< interpret req

exactMatch :: InterpretJsonRequest -> TestName -> Request JSON.Value -> Response JSON.Value -> TestTree
exactMatch interpret testName req expected = testResponse interpret testName req (\actual -> actual @?= expected)
