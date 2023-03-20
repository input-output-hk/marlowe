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
import qualified Data.Text as T
import Marlowe.Utils (showJson)

type Seed = Int
type Size = Int
data Request transport
  = TestRoundtripSerialization TypeId transport
  | GenerateRandomValue TypeId Size Seed
  | FixInterval (Integer, Integer) (C.State_ext ())
  | ReduceContractUntilQuiescent (C.Environment_ext ()) (C.State_ext ()) C.Contract
  | ComputeTransaction (C.Transaction_ext ()) (C.State_ext ()) C.Contract
  | PlayTrace Integer C.Contract [C.Transaction_ext ()]
  | EvalValue (C.Environment_ext ()) (C.State_ext ()) C.Value

instance ToJSON (Request JSON.Value) where
  toJSON (TestRoundtripSerialization t v) = object
    [ "request" .= JSON.String "test-roundtrip-serialization"
    , "typeId" .= toJSON t
    , "json"  .= v
    ]
  toJSON (GenerateRandomValue t size seed) = object
    [ "request" .= JSON.String "generate-random-value"
    , "typeId" .= toJSON t
    , "seed" .= toJSON seed
    , "size" .= toJSON size
    ]
  toJSON (ReduceContractUntilQuiescent env state c) = object
    [ "request" .= JSON.String "compute-transaction"
    , "environment" .= toJSON env
    , "state" .= toJSON state
    , "coreContract" .= toJSON c
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
  toJSON (EvalValue env state val) = object
    [ "request" .= JSON.String "eval-value"
    , "environment" .= toJSON env
    , "state" .= toJSON state
    , "value" .= toJSON val
    ]
  toJSON (FixInterval interval state) = object
    [ "request" .= JSON.String "eval-value"
    , "interval" .= toJSON interval
    , "state" .= toJSON state
    ]

data Response transport
  = InvalidRequest String
  | UnknownRequest
  | RequestResponse transport
  | RequestNotImplemented
  | RequestTimeOut
  | ResponseFailure String
    deriving (Eq)

instance Show (Response JSON.Value) where
  show (InvalidRequest err) = "(InvalidRequest " ++ err ++ ")"
  show UnknownRequest = "UnknownRequest"
  show (RequestResponse j) = "(RequestResponse " ++ showJson j ++ ")"
  show RequestNotImplemented = "RequestNotImplemented"
  show RequestTimeOut = "RequestTimeOut"
  show (ResponseFailure err) = "(ResponseFailure " ++ err ++ ")"

instance FromJSON (Response JSON.Value) where
    parseJSON (JSON.String "UnknownRequest") = return UnknownRequest
    parseJSON (JSON.String "RequestNotImplemented") = return RequestNotImplemented
    parseJSON (JSON.Object v) = asError <|> asSuccess
        where
        asError = InvalidRequest <$> v .: "invalid-request"
        asSuccess = RequestResponse <$> v .: "request-response"
    parseJSON _ = fail "Response must be either a string or an object"


instance ToJSON (Response JSON.Value) where
  toJSON UnknownRequest = JSON.String "UnknownRequest"
  toJSON RequestNotImplemented = JSON.String "RequestNotImplemented"
  toJSON RequestTimeOut = JSON.String "RequestTimeOut"

  toJSON (InvalidRequest err) = object
    [ "invalid-request" .= JSON.String (T.pack err)
    ]
  toJSON (RequestResponse res) = object
    [ "request-response" .= res

    ]
  toJSON (ResponseFailure err) = object
    [ "invalid-request" .= JSON.String (T.pack err)
    ]


parseValidResponse :: FromJSON a => Response JSON.Value -> Either String a
parseValidResponse (InvalidRequest err) = Left $ "Invalid request: " ++ err
parseValidResponse UnknownRequest = Left $ "Unknown request"
parseValidResponse RequestNotImplemented = Left $ "Request not implemented"
parseValidResponse RequestTimeOut = Left $ "Request timed out"
parseValidResponse (ResponseFailure err) = Left $ "Problem processing the response: " ++ err

parseValidResponse (RequestResponse v) = case fromJSON v of
  (Error err) -> Left $ "Invalid response: " ++ err
  (Success a) -> Right a

type InterpretJsonRequest = Request JSON.Value -> IO (Response JSON.Value)

testResponse :: InterpretJsonRequest -> TestName -> Request JSON.Value -> (Response JSON.Value -> Assertion) -> TestTree
testResponse interpret testName req assertion =
  testCase testName $ assertion =<< interpret req

exactMatch :: InterpretJsonRequest -> TestName -> Request JSON.Value -> Response JSON.Value -> TestTree
exactMatch interpret testName req expected = testResponse interpret testName req (\actual -> actual @?= expected)
