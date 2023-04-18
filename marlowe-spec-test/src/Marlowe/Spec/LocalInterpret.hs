{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.LocalInterpret
 ( interpretLocal
 )
 where

import qualified Arith (Int (..))
import Data.Aeson (FromJSON, Result (..), ToJSON)
import qualified Data.Aeson as JSON
import Data.Data (Proxy)
import qualified Marlowe.Spec.Core.Generators as Gen
import Marlowe.Spec.Core.Serialization.Json (SerializationResponse (..))
import Marlowe.Spec.Interpret (Request (..), Response (..))
import Marlowe.Spec.TypeId (TypeId (..), fromTypeName)
import Semantics
  ( computeTransaction,
    evalObservation,
    evalValue,
    playTrace
  )
import SemanticsTypes (Party (..), Token (..))
import Test.QuickCheck (Arbitrary (..))
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.Random (mkQCGen)

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
    $ playTrace (Arith.Int_of_integer t) c is
interpretLocal (EvalValue env state val) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ evalValue env state val
interpretLocal (EvalObservation env state obs) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ evalObservation env state obs
interpretLocal (ComputeTransaction t s c) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ computeTransaction t s c
interpretLocal (GenerateRandomValue t@(TypeId name _) size seed) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ case name of
      "Core.Token" -> Gen.RandomValue $ JSON.toJSON (generate' arbitrary :: Token)
      "Core.Party" -> Gen.RandomValue $ JSON.toJSON (generate' arbitrary :: Party)
      _            -> Gen.UnknownType t
  where
  generate' (MkGen g) = g (mkQCGen seed) size

localJsonRoundtripSerialization :: TypeId -> JSON.Value -> SerializationResponse JSON.Value
localJsonRoundtripSerialization t@(TypeId name proxy) v = case fromTypeName name of
      Nothing  -> UnknownType t
      (Just _) -> roundtrip proxy
    where
    roundtrip :: forall a. ToJSON a => FromJSON a => Proxy a -> SerializationResponse JSON.Value
    roundtrip _  = case JSON.fromJSON v :: Result a of
            Error str -> SerializationError str
            Success c ->  SerializationSuccess $ JSON.toJSON c
