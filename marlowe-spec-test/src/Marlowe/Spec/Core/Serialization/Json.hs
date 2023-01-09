{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.Serialization.Json where

import Control.Applicative ((<|>))
import Control.Monad (join)
import Data.Aeson.Types (Result(..), ToJSON(..), FromJSON(..))
import Data.Aeson (object, (.=), (.:), withObject)
import qualified Data.Aeson.Types as JSON
import Data.Text as T
import Data.Proxy (Proxy(..))
import MarloweCoreJson
import GHC.Stack (HasCallStack)
import Test.Tasty (TestTree, testGroup)
import Marlowe.Spec.Interpret (Response (..), InterpretJsonRequest, Request (..), testResponse)
import Marlowe.Spec.TypeId (TypeId(..), HasTypeId (..))
import Test.Tasty.HUnit (Assertion, assertBool, testCase, (@=?))
import qualified SemanticsTypes as C
import QuickCheck.GenT (runGenT, MonadGen (resize))
import Marlowe.Spec.Core.Arbitrary (genToken, genParty, genPayee, genChoiceId, genBound, genValue, genObservation, genAction, genContract, genInput, genTransaction, genPayment, genState, genTransactionWarning, genIntervalError, genTransactionError, genTransactionOutput)
import Test.QuickCheck (generate, counterexample)
import Test.Tasty.QuickCheck (testProperty)
import Test.QuickCheck.Monadic (monadicIO, run, PropertyM, assert, monitor)


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

tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Json Serialization"
  [ exampleTest i
  , arbitraryTests i
  ]

exampleTest :: InterpretJsonRequest -> TestTree
exampleTest i = testGroup "Examples"
  [ testCase "Bound example" $ unitRoundtripTest i exampleBound
  , valueExamples i
  , observationTests i
  , invalidType i
  ]

arbitraryTests :: InterpretJsonRequest -> TestTree
arbitraryTests i = testGroup "Arbitrary"
  [ arbitraryTokenTest i
  , arbitraryPartyTest i
  , arbitraryPayeeTest i
  , arbitraryChoiceIdTest i
  , arbitraryBoundTest i
  , arbitraryValueTest i
  , arbitraryObservationTest i
  , arbitraryActionTest i
  , arbitraryContractTest i
  , arbitraryInputTest i
  , arbitraryTransactionTest i
  , arbitraryPaymentTest i
  , arbitraryStateTest i
  , arbitraryTransactionWarningTest i
  , arbitraryIntervalErrorTest i
  , arbitraryTransactionErrorTest i
  , arbitraryTransactionOutputTest i
  ]

valueExamples :: InterpretJsonRequest -> TestTree
valueExamples i = testGroup "Value examples"
  [ testCase "Constant" $ unitRoundtripTest i constantExample
  , testCase "Interval start" $ unitRoundtripTest i intervalStartExample
  , testCase "Interval end" $ unitRoundtripTest i intervalEndExample
  , testCase "Add" $ unitRoundtripTest i addExample
  , testCase "Sub" $ unitRoundtripTest i subExample
  , testCase "Mul" $ unitRoundtripTest i mulExample
  , testCase "Div" $ unitRoundtripTest i divExample
  , testCase "Negate" $ unitRoundtripTest i negateExample
  , testCase "Use" $ unitRoundtripTest i useValueExample
  , testCase "Cond" $ unitRoundtripTest i condExample
  , testResponse i "Invalid value"
    (TestRoundtripSerialization
      (TypeId "Core.Value" (Proxy @C.Value))
      (JSON.String "invalid value")
    )
    assertSerializationError
  ]

observationTests :: InterpretJsonRequest -> TestTree
observationTests i = testGroup "Observation examples"
  [ testCase "True" $ unitRoundtripTest i trueExample
  , testCase "False" $ unitRoundtripTest i falseExample
  , testCase "And" $ unitRoundtripTest i andExample
  , testCase "Or" $ unitRoundtripTest i orExample
  , testCase "Not" $ unitRoundtripTest i notExample
  , testCase "Value GE" $ unitRoundtripTest i valueGEExample
  , testCase "Value GT" $ unitRoundtripTest i valueGTExample
  , testCase "Value LT" $ unitRoundtripTest i valueLTExample
  , testCase "Value LE" $ unitRoundtripTest i valueLEExample
  , testCase "Value EQ" $ unitRoundtripTest i valueEQExample
  , testResponse i "Invalid observation"
    (TestRoundtripSerialization (TypeId "Core.Observation" (Proxy :: Proxy C.Observation)) (JSON.String "invalid"))
    assertSerializationError

  ]

invalidType :: InterpretJsonRequest -> TestTree
invalidType i = testResponse i "Invalid type"
    (TestRoundtripSerialization (TypeId "InvalidType" (Proxy :: Proxy ())) (JSON.String "invalid"))
    assertUnknownType

unitRoundtripTest :: (HasTypeId a, ToJSON a) => InterpretJsonRequest -> a -> Assertion
unitRoundtripTest interpret a = do
  res <- interpret serializationRequest
  successResponse @=? res
  where
  serializationRequest = TestRoundtripSerialization (getTypeId a) $ toJSON a
  successResponse = RequestResponse $ toJSON $ SerializationSuccess $ toJSON a

propertyRoundtripTest :: (HasTypeId a, ToJSON a) => InterpretJsonRequest -> a -> PropertyM IO ()
propertyRoundtripTest interpret a = do
  res <- run $ interpret serializationRequest
  monitor (
    counterexample $
      "Request: " ++ show serializationRequest ++ "\n" ++
      "Expected: " ++ show successResponse ++ "\n" ++
      "Actual: " ++ show res
    )
  assert $ successResponse == res
  where
  serializationRequest = TestRoundtripSerialization (getTypeId a) $ toJSON a
  successResponse = RequestResponse $ toJSON $ SerializationSuccess $ toJSON a


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

arbitraryTokenTest :: InterpretJsonRequest -> TestTree
arbitraryTokenTest i = testProperty "Token" $ monadicIO do
  -- Any token that is randomly generated by the interpreter should also pass the roundtrip test
  token <- run $ join $ generate $ runGenT $ genToken i
  propertyRoundtripTest i token

arbitraryPartyTest :: InterpretJsonRequest -> TestTree
arbitraryPartyTest i = testProperty "Party" $ monadicIO do
  -- Any party that is randomly generated by the interpreter should also pass the roundtrip test
  party <- run $ join $ generate $ runGenT $ genParty i
  propertyRoundtripTest i party

arbitraryPayeeTest :: InterpretJsonRequest -> TestTree
arbitraryPayeeTest i = testProperty "Payee" $ monadicIO do
  payee <- run $ join $ generate $ runGenT $ genPayee i
  propertyRoundtripTest i payee

arbitraryChoiceIdTest :: InterpretJsonRequest -> TestTree
arbitraryChoiceIdTest i = testProperty "ChoiceId" $ monadicIO do
  choiceId <- run $ join $ generate $ runGenT $ genChoiceId i
  propertyRoundtripTest i choiceId

arbitraryBoundTest :: InterpretJsonRequest -> TestTree
arbitraryBoundTest i = testProperty "Bound" $ monadicIO do
  bound <- run $ generate genBound
  propertyRoundtripTest i bound

arbitraryValueTest :: InterpretJsonRequest -> TestTree
arbitraryValueTest i = testProperty "Value" $ monadicIO do
  value <- run $ join $ generate $ resize 15 $ runGenT $ genValue i
  propertyRoundtripTest i value

arbitraryObservationTest :: InterpretJsonRequest -> TestTree
arbitraryObservationTest i = testProperty "Observation" $ monadicIO do
  observation <- run $ join $ generate $ resize 15 $ runGenT $ genObservation i
  propertyRoundtripTest i observation

arbitraryActionTest :: InterpretJsonRequest -> TestTree
arbitraryActionTest i = testProperty "Action" $ monadicIO do
  action <- run $ join $ generate $ resize 15 $ runGenT $ genAction i
  propertyRoundtripTest i action

arbitraryContractTest :: InterpretJsonRequest -> TestTree
arbitraryContractTest i = testProperty "Contract" $ monadicIO do
  contract <- run $ join $ generate $ resize 10 $ runGenT $ genContract i
  propertyRoundtripTest i contract

arbitraryInputTest :: InterpretJsonRequest -> TestTree
arbitraryInputTest i = testProperty "Input" $ monadicIO do
  input <- run $ join $ generate $ runGenT $ genInput i
  propertyRoundtripTest i input

arbitraryTransactionTest :: InterpretJsonRequest -> TestTree
arbitraryTransactionTest i = testProperty "Transaction" $ monadicIO do
  tx <- run $ join $ generate $ runGenT $ genTransaction i
  propertyRoundtripTest i tx

arbitraryPaymentTest :: InterpretJsonRequest -> TestTree
arbitraryPaymentTest i = testProperty "Payment" $ monadicIO do
  payment <- run $ join $ generate $ runGenT $ genPayment i
  propertyRoundtripTest i payment

arbitraryStateTest :: InterpretJsonRequest -> TestTree
arbitraryStateTest i = testProperty "State" $ monadicIO do
  state <- run $ join $ generate $ runGenT $ genState i
  propertyRoundtripTest i state

arbitraryTransactionWarningTest :: InterpretJsonRequest -> TestTree
arbitraryTransactionWarningTest i = testProperty "TransactionWarning" $ monadicIO do
  warning <- run $ join $ generate $ runGenT $ genTransactionWarning i
  propertyRoundtripTest i warning

arbitraryIntervalErrorTest :: InterpretJsonRequest -> TestTree
arbitraryIntervalErrorTest i = testProperty "IntervalError" $ monadicIO do
  warning <- run $ generate $ genIntervalError
  propertyRoundtripTest i warning

arbitraryTransactionErrorTest :: InterpretJsonRequest -> TestTree
arbitraryTransactionErrorTest i = testProperty "TransactionError" $ monadicIO do
  txError <- run $ generate $ genTransactionError
  propertyRoundtripTest i txError

arbitraryTransactionOutputTest :: InterpretJsonRequest -> TestTree
arbitraryTransactionOutputTest i = testProperty "TransactionOutput" $ monadicIO do
  out <- run $ join $ generate $ runGenT $ genTransactionOutput i
  propertyRoundtripTest i out



