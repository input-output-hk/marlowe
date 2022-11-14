{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Marlowe.Spec.Core.Serialization.Json where

import Control.Applicative ((<|>))
import Data.Aeson.Types (Result(..), ToJSON(..), FromJSON(..))
import Data.Aeson (object, (.=), (.:), withObject)
import qualified Data.Aeson.Types as JSON
import Data.Text as T
import Data.Proxy (Proxy(..))
import MarloweCoreJson
import GHC.Stack (HasCallStack)
import Test.Tasty (TestTree, testGroup)
import Marlowe.Spec.Interpret (Response (..), InterpretJsonRequest, exactMatch, Request (..), testResponse)
import Marlowe.Spec.TypeId (TypeId(..), HasTypeId (..))
import Test.Tasty.Providers (TestName)
import Test.Tasty.HUnit (Assertion, assertBool)
import qualified SemanticsTypes as C


data SerializationResponse transport
  = SerializationSuccess transport
  | UnknownType TypeId
  | SerializationError String
  deriving (Eq)

instance ToJSON (SerializationResponse JSON.Value) where
  toJSON (SerializationSuccess result) = object
    [ "serialization-success" .= result
    ]
  toJSON (UnknownType t) = object
    [ "unknown-type" .= toJSON t
    ]
  toJSON (SerializationError err) = object
    [ "serialization-error" .= JSON.String (T.pack err)
    ]

instance FromJSON (SerializationResponse JSON.Value) where
  parseJSON = withObject "SerializationResponse" $
      \v -> asSuccess v <|> asUnknownType v <|> asError v
    where
    asSuccess v = SerializationSuccess <$> v .: "serialization-success"
    asUnknownType v = UnknownType <$> v .: "unknown-type"
    asError v = SerializationError <$> v .: "serialization-error"

localJsonRoundtripSerialization :: TypeId -> JSON.Value -> SerializationResponse JSON.Value
localJsonRoundtripSerialization (TypeId _ p) v = roundtrip p
    where
    roundtrip :: forall a. ToJSON a => FromJSON a => Proxy a -> SerializationResponse JSON.Value
    roundtrip _  = case JSON.fromJSON v :: Result a of
            Error str -> SerializationError str
            Success c ->  SerializationSuccess $ JSON.toJSON c


tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Json Serialization"
  [ roundtripExampleTest i "Bound example" condExample
  , valueTests i
  , observationTests i
  , invalidType i
  ]

valueTests :: InterpretJsonRequest -> TestTree
valueTests i = testGroup "Value examples"
  [ roundtripExampleTest i "Constant" constantExample
  , roundtripExampleTest i "Interval start" intervalStartExample
  , roundtripExampleTest i "Interval end" intervalEndExample
  , roundtripExampleTest i "Add" addExample
  , roundtripExampleTest i "Sub" subExample
  , roundtripExampleTest i "Mul" mulExample
  , roundtripExampleTest i "Div" divExample
  , roundtripExampleTest i "Negate" negateExample
  -- , roundtripExampleTest i "Choice value" choiceValueExample
  , roundtripExampleTest i "Use" useValueExample
  , roundtripExampleTest i "Cond" condExample
  -- ,roundtripExampleTest i "Available money" availableMoneyExample
  , testResponse i "Invalid value"
    (TestRoundtripSerialization (TypeId "Core.Value" (Proxy :: Proxy C.Value)) (JSON.String "invalid"))
    assertSerializationError
  ]

observationTests :: InterpretJsonRequest -> TestTree
observationTests i = testGroup "Observation examples"
  [ roundtripExampleTest i "True" trueExample
  , roundtripExampleTest i "False" falseExample
  , roundtripExampleTest i "And" andExample
  , roundtripExampleTest i "Or" orExample
  , roundtripExampleTest i "Not" notExample
  -- , roundtripExampleTest i "Chose" choseExample
  , roundtripExampleTest i "Value GE" valueGEExample
  , roundtripExampleTest i "Value GT" valueGTExample
  , roundtripExampleTest i "Value LT" valueLTExample
  , roundtripExampleTest i "Value LE" valueLEExample
  , roundtripExampleTest i "Value EQ" valueEQExample
  , testResponse i "Invalid observation"
    (TestRoundtripSerialization (TypeId "Core.Observation" (Proxy :: Proxy C.Observation)) (JSON.String "invalid"))
    assertSerializationError

  ]

invalidType :: InterpretJsonRequest -> TestTree
invalidType i = testResponse i "Invalid type"
    (TestRoundtripSerialization (TypeId "InvalidType" (Proxy :: Proxy ())) (JSON.String "invalid"))
    assertUnknownType

roundtripExampleTest :: (HasTypeId a, ToJSON a) => InterpretJsonRequest -> TestName -> a -> TestTree
roundtripExampleTest i name example = exactMatch i name (serializationRequest example) (serializationSuccess example)
  where
  serializationRequest a = TestRoundtripSerialization (getTypeId a) $ toJSON a
  serializationSuccess a = RequestResponse $ JSON.toJSON $ SerializationSuccess $ JSON.toJSON a

assertSerializationError :: HasCallStack => Response JSON.Value -> Assertion
assertSerializationError = assertBool "The serialization response should be SerializationError" . isSerializationError

isSerializationError :: Response JSON.Value -> Bool
isSerializationError (RequestResponse res) = case JSON.fromJSON res :: Result (SerializationResponse JSON.Value) of
  (Success (SerializationError _)) -> True
  _ -> False
isSerializationError _ = False

assertUnknownType :: HasCallStack => Response JSON.Value -> Assertion
assertUnknownType = assertBool "The serialization response should be UnknownType" . isUnknownType

isUnknownType :: Response JSON.Value -> Bool
isUnknownType (RequestResponse res) = case JSON.fromJSON res :: Result (SerializationResponse JSON.Value) of
  (Success (UnknownType _)) -> True
  _ -> False
isUnknownType _ = False
