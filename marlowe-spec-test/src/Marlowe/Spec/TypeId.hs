{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}

module Marlowe.Spec.TypeId (TypeId(..), HasTypeId(..), fromTypeName) where

import Data.Aeson (ToJSON)
import Data.Aeson.Types (FromJSON(..), ToJSON (..))
import qualified SemanticsTypes as C
import qualified Semantics as C
import MarloweCoreJson()
import Data.Data (Proxy(..))
import qualified Data.Aeson as JSON
import qualified Data.Text as T

data TypeId = forall a. (ToJSON a, FromJSON a) => TypeId String (Proxy a)

instance Show TypeId where
  show (TypeId name _) = name

instance Eq TypeId where
  (TypeId t1 _) == (TypeId t2 _) = t1 == t2

fromTypeName :: String -> Maybe TypeId
fromTypeName name = case name of
  "Core.Action" -> Just $ TypeId "Core.Action" (Proxy :: Proxy C.Action)
  "Core.Bound" -> Just $ TypeId "Core.Bound" (Proxy :: Proxy C.Bound)
  "Core.Case" -> Just $ TypeId "Core.Case" (Proxy :: Proxy C.Case)
  "Core.ChoiceId" -> Just $ TypeId "Core.ChoiceId" (Proxy :: Proxy C.ChoiceId)
  "Core.Contract" -> Just $ TypeId "Core.Contract" (Proxy :: Proxy C.Contract)
  "Core.Token" -> Just $ TypeId "Core.Token" (Proxy :: Proxy C.Token)
  "Core.Payee" -> Just $ TypeId "Core.Payee" (Proxy :: Proxy C.Payee)
  "Core.Input" -> Just $ TypeId "Core.Input" (Proxy :: Proxy C.Input)
  "Core.Observation" -> Just $ TypeId "Core.Observation" (Proxy :: Proxy C.Observation)
  "Core.Value" -> Just $ TypeId "Core.Value" (Proxy :: Proxy C.Value)
  "Core.Payment" -> Just $ TypeId "Core.Payment" (Proxy :: Proxy C.Payment)
  "Core.Party" -> Just $ TypeId "Core.Party" (Proxy :: Proxy C.Party)
  "Core.State" -> Just $ TypeId "Core.State" (Proxy :: Proxy (C.State_ext ()))
  "Core.TransactionError" -> Just $ TypeId "Core.TransactionError" (Proxy :: Proxy C.TransactionError)
  "Core.TransactionOutput" -> Just $ TypeId "Core.TransactionOutput" (Proxy :: Proxy C.TransactionOutput)
  "Core.TransactionWarning" -> Just $ TypeId "Core.TransactionWarning" (Proxy :: Proxy C.TransactionWarning)
  "Core.IntervalError" -> Just $ TypeId "Core.IntervalError" (Proxy :: Proxy C.IntervalError)
  "Core.Transaction" -> Just $ TypeId "Core.Transaction" (Proxy :: Proxy (C.Transaction_ext ()))
  _ -> Nothing


instance ToJSON TypeId where
  toJSON (TypeId s _) = JSON.String $ T.pack s

instance FromJSON TypeId where
  parseJSON (JSON.String s) = case fromTypeName (T.unpack s) of
    Just t -> pure t
    Nothing -> pure $ TypeId (T.unpack s) (Proxy :: Proxy ())
  parseJSON _ = fail "TypeId should be a string"

class HasTypeId a where
  getTypeId :: a -> TypeId

instance HasTypeId C.Action where
  getTypeId _ = TypeId "Core.Action" (Proxy :: Proxy C.Action)

instance HasTypeId C.Bound where
  getTypeId _ = TypeId "Core.Bound" (Proxy :: Proxy C.Bound)

instance HasTypeId C.Case where
  getTypeId _ = TypeId "Core.Case" (Proxy :: Proxy C.Case)

instance HasTypeId C.ChoiceId where
  getTypeId _ = TypeId "Core.ChoiceId" (Proxy :: Proxy C.ChoiceId)

instance HasTypeId C.Contract where
  getTypeId _ = TypeId "Core.Contract" (Proxy :: Proxy C.Contract)

instance HasTypeId C.Token where
  getTypeId _ = TypeId "Core.Token" (Proxy :: Proxy C.Token)

instance HasTypeId C.Payee where
  getTypeId _ = TypeId "Core.Payee" (Proxy :: Proxy C.Payee)

instance HasTypeId C.Input where
  getTypeId _ = TypeId "Core.Input" (Proxy :: Proxy C.Input)

instance HasTypeId C.Observation where
  getTypeId _ = TypeId "Core.Observation" (Proxy :: Proxy C.Observation)

instance HasTypeId C.Value where
  getTypeId _ = TypeId "Core.Value" (Proxy :: Proxy C.Value)

instance HasTypeId C.Payment where
  getTypeId _ = TypeId "Core.Payment" (Proxy :: Proxy C.Payment)

instance HasTypeId C.Party where
  getTypeId _ = TypeId "Core.Party" (Proxy :: Proxy C.Party)

instance HasTypeId (C.State_ext ()) where
  getTypeId _ = TypeId "Core.State" (Proxy :: Proxy (C.State_ext ()))

instance HasTypeId C.TransactionError where
  getTypeId _ = TypeId "Core.TransactionError" (Proxy :: Proxy C.TransactionError)

instance HasTypeId C.TransactionOutput where
  getTypeId _ = TypeId "Core.TransactionOutput" (Proxy :: Proxy C.TransactionOutput)

instance HasTypeId C.TransactionWarning where
  getTypeId _ = TypeId "Core.TransactionWarning" (Proxy :: Proxy C.TransactionWarning)

instance HasTypeId (C.Transaction_ext ()) where
  getTypeId _ = TypeId "Core.Transaction" (Proxy :: Proxy (C.Transaction_ext ()))

instance HasTypeId C.IntervalError where
  getTypeId _ = TypeId "Core.IntervalError" (Proxy :: Proxy C.IntervalError)


