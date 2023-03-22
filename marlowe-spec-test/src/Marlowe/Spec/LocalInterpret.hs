{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Marlowe.Spec.LocalInterpret where

import Arith (Int(..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Interpret (Response(..), Request(..))
import Semantics (playTrace, computeTransaction, evalValue, evalObservation)
import Marlowe.Spec.TypeId (TypeId (..), fromTypeName)
import Marlowe.Spec.Core.Serialization.Json
import Data.Data (Proxy)
import Data.Aeson (Result (..),FromJSON,ToJSON)
import SemanticsTypes (Token(Token), Party (..))
import Test.QuickCheck (Gen, frequency, Arbitrary (arbitrary))
import qualified Marlowe.Spec.Core.Arbitrary as RandomResponse
import Marlowe.Spec.Core.Arbitrary (arbitraryFibonacci)
import Test.QuickCheck.Gen (Gen(..))
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
    $ playTrace (Int_of_integer t) c is
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
      "Core.Token" -> RandomResponse.RandomValue $ JSON.toJSON $ generate' arbitraryToken
      "Core.Party" -> RandomResponse.RandomValue $ JSON.toJSON $ generate' arbitraryParty
      _ -> RandomResponse.UnknownType t
  where
  generate' (MkGen g) = g (mkQCGen seed) size


arbitraryToken :: Gen Token
arbitraryToken =
  frequency
    [(50, pure $ Token "" "")
    ,(50, Token <$> arbitrary <*> arbitrary)
    ]


-- | Some role names.
randomRoleNames :: [String]
randomRoleNames =
  [
    "Cy"
  , "Noe"
  , "Sten"
  , "Cara"
  , "Alene"
  , "Hande"
  , ""
  , "I"
  , "Zakkai"
  , "Laurent"
  , "Prosenjit"
  , "Dafne Helge Mose"
  , "Nonso Ernie Blanka"
  , "Umukoro Alexander Columb"
  , "Urbanus Roland Alison Ty Ryoichi"
  , "Alcippe Alende Blanka Roland Dafne"  -- NB: Too long for Cardano ledger.
  ]


arbitraryParty :: Gen Party
arbitraryParty = do
  isAddress <- frequency [(2, pure True), (8, pure False)]
  if isAddress
    then Address <$> arbitrary
    else Role <$> arbitraryFibonacci randomRoleNames

localJsonRoundtripSerialization :: TypeId -> JSON.Value -> SerializationResponse JSON.Value
localJsonRoundtripSerialization t@(TypeId name proxy) v = case fromTypeName name of
      Nothing -> UnknownType t
      (Just _) -> roundtrip proxy
    where
    roundtrip :: forall a. ToJSON a => FromJSON a => Proxy a -> SerializationResponse JSON.Value
    roundtrip _  = case JSON.fromJSON v :: Result a of
            Error str -> SerializationError str
            Success c ->  SerializationSuccess $ JSON.toJSON c

