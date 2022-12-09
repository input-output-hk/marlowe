{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}

module Marlowe.Spec.Core.Arbitrary where

import SemanticsTypes (Token(..), Party)
import QuickCheck.GenT (GenT, frequency)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import Data.Data (Proxy(..))
import Marlowe.Spec.TypeId (TypeId(..))
import Control.Monad.IO.Class (liftIO)
import Control.Exception (throwIO, Exception)
import Data.Aeson (FromJSON(..), withObject, (.:), (.=))
import Control.Applicative ((<|>))
import Data.Aeson (ToJSON (..), object)

data RandomResponse a
  = RandomValue a
  | UnknownType TypeId


instance ToJSON a => ToJSON (RandomResponse a) where
  toJSON (RandomValue v) = object
    [ "value" .= v
    ]
  toJSON (UnknownType t) = object
    [ "unknown-type" .= toJSON t
    ]

instance FromJSON a => FromJSON (RandomResponse a) where
  parseJSON =  withObject "RandomResponse" $
     \v -> asRandomValue v <|> asUnknownType v
    where
    asRandomValue v = RandomValue <$> v .: "value"
    asUnknownType v = UnknownType <$> v .: "unknown-type"

data GenerateRandomValueException = GenerateRandomValueException String
  deriving (Show, Exception)

arbitraryToken :: InterpretJsonRequest -> GenT IO Token
arbitraryToken interpret = liftIO do
  res <- interpret (GenerateRandomValue $ TypeId "Core.Token" (Proxy :: Proxy Token))
  case parseValidResponse res of
    Left err -> throwIO $ GenerateRandomValueException err
    Right (UnknownType _) -> throwIO $ GenerateRandomValueException "Client process doesn't know how to generate Core.Token"
    Right (RandomValue t) -> pure t


arbitraryParty :: InterpretJsonRequest -> GenT IO Party
arbitraryParty interpret = liftIO do
  res <- interpret (GenerateRandomValue $ TypeId "Core.Party" (Proxy :: Proxy Party))
  case parseValidResponse res of
    Left err -> throwIO $ GenerateRandomValueException err
    Right (UnknownType _) -> throwIO $ GenerateRandomValueException "Client process doesn't know how to generate Core.Party"
    Right (RandomValue t) -> pure t