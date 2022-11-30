{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Marlowe.Spec.LocalInterpret where

import Arith (Int(..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Interpret (Response(..), Request(..))
import Semantics (playTrace, computeTransaction)
import Marlowe.Spec.TypeId (TypeId (..), fromTypeName)
import Marlowe.Spec.Core.Serialization.Json
import Data.Data (Proxy)
import Data.Aeson (Result (..),FromJSON,ToJSON)
import SemanticsTypes (Token(Token))
import Test.QuickCheck (Gen, frequency, Arbitrary (arbitrary), generate)
import qualified Marlowe.Spec.Core.Arbitrary as RandomResponse


interpretLocal :: Request JSON.Value -> IO (Response JSON.Value)
interpretLocal (TestRoundtripSerialization t v) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ localJsonRoundtripSerialization t v
interpretLocal (PlayTrace t c is) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ playTrace (Int_of_integer t) c is
interpretLocal (ComputeTransaction t s c) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ computeTransaction t s c
interpretLocal (GenerateRandomValue t@(TypeId name _)) =
  RequestResponse
    <$> JSON.toJSON
    <$> case name of
      "Core.Token" -> RandomResponse.RandomValue <$> JSON.toJSON <$> generate arbitraryToken
      _ -> pure $ RandomResponse.UnknownType t


arbitraryToken :: Gen Token
arbitraryToken =
  frequency
    [(50, pure $ Token "" "")
    ,(50, Token <$> arbitrary <*> arbitrary)
    ]

localJsonRoundtripSerialization :: TypeId -> JSON.Value -> SerializationResponse JSON.Value
localJsonRoundtripSerialization t@(TypeId name proxy) v = case fromTypeName name of
      Nothing -> UnknownType t
      (Just _) -> roundtrip proxy
    where
    roundtrip :: forall a. ToJSON a => FromJSON a => Proxy a -> SerializationResponse JSON.Value
    roundtrip _  = case JSON.fromJSON v :: Result a of
            Error str -> SerializationError str
            Success c ->  SerializationSuccess $ JSON.toJSON c

