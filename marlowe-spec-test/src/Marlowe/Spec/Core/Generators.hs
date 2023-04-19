{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.Core.Generators
  ( genToken
  , genParty
  , genPayee
  , genChoiceId
  , genValue
  , genObservation
  , genPayment
  , genTransaction
  , genInput
  , genAction
  , genState
  , genContract
  , genTransactionOutput
  , genTransactionWarning
  , RandomResponse (..)
  )
  where

import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Control.Monad (liftM2)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import Data.Data (Proxy (..))
import Marlowe.Spec.Core.Arbitrary
  ( arbitraryChoiceName,
    arbitraryInteger,
    arbitraryNonnegativeInteger,
  )
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import Marlowe.Spec.TypeId (TypeId (..))
import QuickCheck.GenT
  ( GenT,
    MonadGen (..),
    frequency,
    resize,
    scale,
    sized,
    suchThat,
    vectorOf,
  )
import Semantics
  ( Payment (..),
    TransactionOutput (..),
    TransactionOutputRecord_ext (..),
    TransactionWarning (..),
    Transaction_ext (..),
  )
import SemanticsGuarantees (valid_state)
import SemanticsTypes
  ( Action (..),
    Case (..),
    ChoiceId (..),
    Contract (..),
    Input (..),
    Observation (..),
    Party (..),
    Payee (..),
    State_ext (..),
    Token (..),
    Value (..),
  )
import Test.QuickCheck (Gen, chooseInt, getSize)
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

genPayee ::  InterpretJsonRequest -> GenT IO Payee
genPayee i = do
  isParty <- liftGen arbitrary
  if isParty
    then Party <$> genParty i
    else Account <$> genParty i

genChoiceId :: InterpretJsonRequest -> GenT IO ChoiceId
genChoiceId i = ChoiceId <$> liftGen arbitraryChoiceName <*> genParty i

genValue :: InterpretJsonRequest -> GenT IO Value
genValue i = sized (
  \case n | n <= 1 ->
            frequency
              [ (80, genConstant)
              , (10, genTimeIntervalStart)
              , (10, genTimeIntervalEnd)
              ]
          | n == 2 ->
            frequency
              [ (45, genConstant)
              , (8, genTimeIntervalStart)
              , (8, genTimeIntervalEnd)
              , (13, genNegValue)
              , (13, genUseValue)
              , (13, genChoiceValue)
              ]
          | otherwise ->
            frequency
              [ ( 8, genAvailableMoney)
              , (14, genConstant)
              , ( 8, resize (n - 1) genNegValue)
              , ( 8, resize (n - 2) genAddValue)
              , ( 8, resize (n - 2) genSubValue)
              , ( 8, resize (n - 2) genMulValue)
              , ( 8, resize (n - 2) genDivValue)
              , (10, genChoiceValue)
              , ( 6, genTimeIntervalStart)
              , ( 6, genTimeIntervalEnd)
              , ( 8, genUseValue)
              , ( 8, resize (n - 3) genCond)
              ]
  )
  where
  genAvailableMoney = AvailableMoney <$> genParty i <*> genToken i
  genConstant = Constant <$> liftGen arbitraryInteger
  genNegValue = NegValue <$> genValue i
  genAddValue = AddValue <$> genValue i <*> genValue i
  genSubValue = SubValue <$> genValue i <*> genValue i
  genMulValue = MulValue <$> genValue i <*> genValue i
  genDivValue = DivValue <$> genValue i <*> genValue i
  genChoiceValue = ChoiceValue <$> genChoiceId i
  genTimeIntervalStart = pure TimeIntervalStart
  genTimeIntervalEnd = pure TimeIntervalEnd
  genUseValue = UseValue <$> liftGen arbitrary
  genCond = Cond <$> genObservation i <*> genValue i <*> genValue i

genObservation :: InterpretJsonRequest -> GenT IO Observation
genObservation i = sized (
  \case n | n <= 1 -> frequency
            [ (10, genChoseSomething)
            , (45, genTrue)
            , (45, genFalse)
            ]
          | otherwise -> frequency
            [ ( 8, resize (n - 2) genAndObs)
            , ( 8, resize (n - 2) genOrObs)
            , ( 8, resize (n - 1) genNotObs)
            , (16, genChoseSomething)
            , ( 8, resize (n - 2) genValueGE)
            , ( 8, resize (n - 2) genValueGT)
            , ( 8, resize (n - 2) genValueLT)
            , ( 8, resize (n - 2) genValueLE)
            , ( 8, resize (n - 2) genValueEQ)
            , (10, genTrue)
            , (10, genFalse)
            ]
  )
  where
  genAndObs = AndObs <$> genObservation i <*> genObservation i
  genOrObs = OrObs <$> genObservation i <*> genObservation i
  genNotObs = NotObs <$> genObservation i
  genChoseSomething = ChoseSomething <$> genChoiceId i
  genValueGE = ValueGE <$> genValue i <*> genValue i
  genValueGT = ValueGT <$> genValue i <*> genValue i
  genValueLT = ValueLT <$> genValue i <*> genValue i
  genValueLE = ValueLE <$> genValue i <*> genValue i
  genValueEQ = ValueEQ <$> genValue i <*> genValue i
  genTrue = pure TrueObs
  genFalse = pure FalseObs

genAction :: InterpretJsonRequest -> GenT IO Action
genAction i = frequency
      [ (7, Deposit <$> genParty i <*> genParty i <*> genToken i <*> genValue i)
      , (2, do
          lSize <- liftGen $ chooseInt (1, 4)
          Choice <$> genChoiceId i <*> vectorOf lSize (liftGen arbitrary)
        )
      , (1, Notify <$> genObservation i)
      ]

genInput :: InterpretJsonRequest -> GenT IO Input
genInput i = frequency
  [ (50, IDeposit <$> genParty i <*> genParty i <*> genToken i <*> liftGen arbitraryInteger)
  , (45, IChoice <$> genChoiceId i <*> liftGen arbitraryInteger )
  , (5, pure INotify)
  ]

genTransaction :: InterpretJsonRequest -> GenT IO (Transaction_ext ())
genTransaction i = do
  lower <- liftGen arbitraryInteger
  extent <- liftGen arbitraryNonnegativeInteger
  iSize <- liftGen $ chooseInt (0, 4)
  inputs <- vectorOf iSize (genInput i)
  pure $ Transaction_ext (lower, lower + extent) inputs ()

genPayment ::  InterpretJsonRequest -> GenT IO Payment
genPayment i = Payment <$> genParty i <*> genPayee i <*> genToken i <*> liftGen arbitraryInteger

(>*<) :: Monad m => GenT m a -> GenT m b -> GenT m (a, b)
genA >*< genB = liftM2 (,) genA genB

genState :: InterpretJsonRequest -> GenT IO (State_ext ())
genState i = rawGen `suchThat` valid_state
  where
  rawGen = sized
    (\n ->  do
      accountSize <- liftGen $ chooseInt (0, min n 4)
      choiceSize <- liftGen $ chooseInt (0, min n 4)
      boundSize <- liftGen $ chooseInt (0, min n 4)
      accounts <- vectorOf accountSize ((genParty i >*< genToken i) >*< liftGen arbitraryNonnegativeInteger)
      choices <- vectorOf choiceSize (genChoiceId i >*< liftGen arbitraryInteger)
      bounds <- vectorOf boundSize (liftGen arbitrary >*< liftGen arbitraryInteger)
      minTime' <- liftGen arbitraryInteger
      pure $ State_ext accounts choices bounds minTime' ()
    )

genTransactionWarning :: InterpretJsonRequest -> GenT IO TransactionWarning
genTransactionWarning i = frequency
  [ ( 30, TransactionNonPositiveDeposit <$> genParty i <*> genParty i <*> genToken i <*> liftGen arbitraryInteger)
  , ( 30, TransactionNonPositivePay <$> genParty i <*> genPayee i <*> genToken i <*> liftGen arbitraryInteger)
  , ( 30, TransactionShadowing <$> liftGen arbitrary <*> liftGen arbitraryInteger <*> liftGen arbitraryInteger)
  , ( 10, pure TransactionAssertionFailed)
  ]

genTransactionOutput :: InterpretJsonRequest -> GenT IO TransactionOutput
genTransactionOutput i =
  frequency
    [ (30, TransactionError <$> liftGen arbitrary),
      ( 70,
        TransactionOutput <$> do
          wSize <- liftGen $ chooseInt (0, 2)
          warnings <- vectorOf wSize $ genTransactionWarning i
          pSize <- liftGen $ chooseInt (0, 2)
          payments <- vectorOf pSize $ genPayment i
          state <- resize 2 $ genState i
          contract <- resize 2 $ genContract i
          pure $ TransactionOutputRecord_ext warnings payments state contract ()
      )
    ]

genCase :: InterpretJsonRequest -> GenT IO Case
genCase i = Case <$> genAction i <*> genContract i

genContract :: InterpretJsonRequest -> GenT IO Contract
genContract i =
  sized
    ( \case
        n
          | n <= 1 -> genClose
          | otherwise ->
              frequency
                [ (30, genClose),
                  (20, genPay n),
                  (15, genIf n),
                  (20, genWhen n),
                  (10, genLet n),
                  (5, genAssert n)
                ]
    )
  where
    genClose = pure Close
    genPay n = Pay <$> genParty i <*> genPayee i <*> genToken i <*> limit (genValue i) <*> resize (n - 1) (genContract i)
    genIf n = If <$> limit (genObservation i) <*> resize (n - 1) (genContract i) <*> resize (n - 1) (genContract i)
    genWhen n = do
      lSize <- liftGen $ chooseInt (0, 3)
      cases <- vectorOf lSize (resize (n - lSize) (genCase i))
      timeout <- liftGen arbitraryInteger
      cont <- resize (n - 1) (genContract i)
      pure $ When cases timeout cont
    genLet n = Let <$> liftGen arbitrary <*> limit (genValue i) <*> resize (n - 1) (genContract i)
    genAssert n = Assert <$> limit (genObservation i) <*> resize (n - 1) (genContract i)
    limit = scale (min 3)
