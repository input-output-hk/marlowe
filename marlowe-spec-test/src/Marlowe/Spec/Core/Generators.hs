{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.Core.Generators
  ( gen
  , genContext
  , RandomResponse (..)
  )
  where

import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Control.Monad (replicateM)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import Data.Data (Proxy (..))
import Data.Function (on)
import Data.List (nubBy)
import Data.Map (fromList)
import Marlowe.Spec.Core.Arbitrary
  ( arbitraryChoiceName,
    arbitraryInteger,
    arbitraryPositiveInteger,
  )
import Marlowe.Spec.Core.SemiArbitrary (Context (..), SemiArbitrary (..))
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import Marlowe.Spec.TypeId (TypeId (..))
import QuickCheck.GenT (GenT, MonadGen (..), elements, frequency, resize, sized)
import SemanticsTypes
  ( ChoiceId (..),
    Party (..),
    Token (..),
  )
import Test.QuickCheck (Gen, getSize)
import Test.QuickCheck.Arbitrary (Arbitrary (..))

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

newtype GenerateRandomValueException = GenerateRandomValueException String
  deriving (Show, Exception)

gen :: SemiArbitrary a => InterpretJsonRequest -> GenT IO a
gen i =  liftGen . semiArbitrary =<< genContext i

arbitrarySeed :: Gen Int
arbitrarySeed = resize 10000 $ choose (1, 10000000)

genToken :: InterpretJsonRequest -> GenT IO Token
genToken interpret = do
  size <- liftGen getSize
  seed <- liftGen arbitrarySeed
  liftIO do
    res <- interpret (GenerateRandomValue (TypeId "Core.Token" (Proxy :: Proxy Token)) size seed)
    case parseValidResponse res of
      Left err -> throwIO $ GenerateRandomValueException err
      Right (UnknownType _) -> throwIO $ GenerateRandomValueException "Client process doesn't know how to generate Core.Token"
      Right (RandomValue t) -> pure t

genParty :: InterpretJsonRequest -> GenT IO Party
genParty interpret = do
  size <- liftGen getSize
  seed <- liftGen arbitrarySeed
  liftIO do
    res <- interpret (GenerateRandomValue (TypeId "Core.Party" (Proxy :: Proxy Party)) size seed)
    case parseValidResponse res of
      Left err -> throwIO $ GenerateRandomValueException err
      Right (UnknownType _) -> throwIO $ GenerateRandomValueException "Client process doesn't know how to generate Core.Party"
      Right (RandomValue t) -> pure t

genContext :: InterpretJsonRequest -> GenT IO Context
genContext interpret = sized \n ->
  let listOf g = choose (1, n) >>= flip replicateM g
      listOfGen = liftGen . listOf
      genParty' = genParty interpret
      genToken' = genToken interpret
   in do
        parties <- listOf genParty'
        tokens <- listOf genToken'
        amounts <- listOfGen arbitraryPositiveInteger
        choiceNames <- listOfGen arbitraryChoiceName
        chosenNums <- listOfGen arbitraryInteger
        choiceIds <-
          listOf $
            ChoiceId
              <$> liftGen (perturb arbitraryChoiceName choiceNames)
              <*> perturb genParty' parties
        valueIds <- listOfGen arbitrary
        values <- listOfGen arbitraryInteger
        times <- listOfGen arbitraryPositiveInteger
        caccounts <-
          fromList . nubBy ((==) `on` fst)
            <$> listOf
              ( (,)
                  <$> ( (,)
                          <$> perturb genParty' parties
                          <*> perturb genToken' tokens
                      )
                  <*> liftGen (perturb arbitraryPositiveInteger amounts)
              )
        cchoices <-
          fromList . nubBy ((==) `on` fst)
            <$> listOf
              ( (,)
                  <$> liftGen (elements choiceIds)
                  <*> liftGen (perturb arbitraryInteger chosenNums)
              )
        cboundValues <-
          fromList . nubBy ((==) `on` fst)
            <$> listOf
              ( (,)
                  <$> liftGen (perturb arbitrary valueIds)
                  <*> liftGen (perturb arbitraryInteger values)
              )
        pure Context {..}
  where
    perturb :: MonadGen g => g a -> [a] -> g a
    perturb g [] = g
    perturb g xs = frequency [(20, g), (80, liftGen $ elements xs)]
