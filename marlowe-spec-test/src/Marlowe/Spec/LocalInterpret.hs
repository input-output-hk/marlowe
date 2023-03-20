{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.LocalInterpret
 ( interpretLocal
 )
 where

import qualified Arith (Int(..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Interpret (Response(..), Request(..))
import Semantics (playTrace, computeTransaction, evalValue, reduceContractUntilQuiescent, fixInterval)
import Marlowe.Spec.TypeId (TypeId (..), fromTypeName)
import Marlowe.Spec.Core.Serialization.Json
import Data.Data (Proxy)
import Data.Aeson (Result (..),FromJSON,ToJSON)
import SemanticsTypes (Token(Token), Party (..), ChoiceId (..), Action (..), Value (..), Payee (..), Observation (..))
import Test.QuickCheck (frequency, Arbitrary (..), suchThat, resize)
import qualified Marlowe.Spec.Core.Arbitrary as RandomResponse
import Marlowe.Spec.Core.Arbitrary (arbitraryFibonacci, arbitraryPositiveInteger, arbitraryChoiceName, shrinkChoiceName)
import Test.QuickCheck.Gen (Gen(..))
import Test.QuickCheck.Random (mkQCGen)
import Test.QuickCheck (sized)

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
interpretLocal (ReduceContractUntilQuiescent e s c) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ reduceContractUntilQuiescent e s c
interpretLocal (ComputeTransaction t s c) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ computeTransaction t s c
interpretLocal (FixInterval (a, b) s) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ fixInterval (Arith.Int_of_integer a, Arith.Int_of_integer b) s
interpretLocal (GenerateRandomValue t@(TypeId name _) size seed) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ case name of
      "Core.Token" -> RandomResponse.RandomValue $ JSON.toJSON $ (generate' arbitrary :: Token)
      "Core.Party" -> RandomResponse.RandomValue $ JSON.toJSON $ (generate' arbitrary :: Party)
      _ -> RandomResponse.UnknownType t
  where
  generate' (MkGen g) = g (mkQCGen seed) size

instance Ord Party where
  compare (Address a) (Address b) = compare a b
  compare (Address _) (Role _) = LT
  compare (Role _) (Address _) = GT
  compare (Role a) (Role b) = compare a b

instance Ord Token where
  compare (Token a1 b1) (Token a2 b2) =
    let res = compare a1 a2
     in case res of
      EQ -> compare b1 b2
      _ -> res

instance Ord ChoiceId where
  compare (ChoiceId a1 b1) (ChoiceId a2 b2) =
    let res = compare a1 a2
     in case res of
      EQ -> compare b1 b2
      _ -> res

instance Arbitrary Token where
  arbitrary =
     do
       isAda <- arbitrary
       if isAda
         then pure $ Token "" ""
         else Token <$> arbitrary <*> arbitrary
  shrink (Token c n)
    | c == "" && n == "" = []
    | otherwise                       = Token "" "" : [Token c' n' | c' <- shrink c, n' <- shrink n]

instance Arbitrary Party where
  arbitrary =
    do
       isPubKeyHash <- frequency [(2, pure True), (8, pure False)]
       if isPubKeyHash
         then Address <$> arbitrary
         else Role <$> arbitraryFibonacci randomRoleNames
  shrink (Address _) = Role <$> randomRoleNames
  shrink (Role _)      = Role <$> randomRoleNames

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

instance Arbitrary Value where
  arbitrary =  sized
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
                , ( 8, resize (n - 1) $ genNegValue)
                , ( 8, resize (n - 2) $ genAddValue)
                , ( 8, resize (n - 2) $ genSubValue)
                , ( 8, resize (n - 2) $ genMulValue)
                , ( 8, resize (n - 2) $ genDivValue)
                , (10, genChoiceValue)
                , ( 6, genTimeIntervalStart)
                , ( 6, genTimeIntervalEnd)
                , ( 8, genUseValue)
                , ( 8, resize (n - 3) $ genCond)
                ]
    where
      genAvailableMoney = AvailableMoney <$> arbitrary <*> arbitrary
      genConstant = Constant <$> arbitraryPositiveInteger
      genNegValue = NegValue <$> arbitrary
      genAddValue = AddValue <$> arbitrary <*> arbitrary
      genSubValue = SubValue <$> arbitrary <*> arbitrary
      genMulValue = MulValue <$> arbitrary <*> arbitrary
      genDivValue = DivValue <$> arbitrary <*> arbitrary
      genChoiceValue = ChoiceValue <$> arbitrary
      genTimeIntervalStart = pure TimeIntervalStart
      genTimeIntervalEnd = pure TimeIntervalEnd
      genUseValue = UseValue <$> arbitrary
      genCond = Cond <$> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary Observation where
  arbitrary =
    frequency
      [
        ( 8, AndObs <$> arbitrary <*> arbitrary)
      , ( 8, OrObs <$> arbitrary <*> arbitrary)
      , ( 8, NotObs <$> arbitrary)
      , (16, ChoseSomething <$> arbitrary)
      , ( 8, ValueGE <$> arbitrary <*> arbitrary)
      , ( 8, ValueGT <$> arbitrary <*> arbitrary)
      , ( 8, ValueLT <$> arbitrary <*> arbitrary)
      , ( 8, ValueLE <$> arbitrary <*> arbitrary)
      , ( 8, ValueEQ <$> arbitrary <*> arbitrary)
      , (10, pure TrueObs)
      , (10, pure FalseObs)
      ]
  shrink (AndObs x y)       = [AndObs x' y | x' <- shrink x] ++ [AndObs x y' | y' <- shrink y]
  shrink (OrObs x y)        = [OrObs x' y | x' <- shrink x] ++ [OrObs x y' | y' <- shrink y]
  shrink (NotObs x)         = NotObs <$> shrink x
  shrink (ChoseSomething c) = ChoseSomething <$> shrink c
  shrink (ValueGE x y)      = [ValueGE x' y | x' <- shrink x] ++ [ValueGE x y' | y' <- shrink y]
  shrink (ValueGT x y)      = [ValueGT x' y | x' <- shrink x] ++ [ValueGT x y' | y' <- shrink y]
  shrink (ValueLT x y)      = [ValueLT x' y | x' <- shrink x] ++ [ValueLT x y' | y' <- shrink y]
  shrink (ValueLE x y)      = [ValueLE x' y | x' <- shrink x] ++ [ValueLE x y' | y' <- shrink y]
  shrink (ValueEQ x y)      = [ValueEQ x' y | x' <- shrink x] ++ [ValueEQ x y' | y' <- shrink y]
  shrink _                  = []

instance Arbitrary ChoiceId where
  arbitrary = ChoiceId <$> arbitraryChoiceName <*> arbitrary
  shrink (ChoiceId n p) = [ChoiceId n' p' | n' <- shrinkChoiceName n, p' <- shrink p]

instance Arbitrary Payee where
  arbitrary =
    do
      isParty <- arbitrary
      if isParty
        then Party <$> arbitrary
        else Account <$> arbitrary
  shrink (Party x)   = Party <$> shrink x
  shrink (Account x) = Account <$> shrink x

instance Arbitrary Action where
  arbitrary =
    frequency
      [
        (3, Deposit <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)
      , (6, Choice <$> arbitrary <*> arbitrary `suchThat` ((< 5) . length))
      , (1, Notify <$> arbitrary)
      ]
  shrink (Deposit a p t x) = [Deposit a' p t x | a' <- shrink a] ++ [Deposit a p' t x | p' <- shrink p] ++ [Deposit a p t' x | t' <- shrink t] ++ [Deposit a p t x' | x' <- shrink x]
  shrink (Choice c b) = [Choice c' b | c' <- shrink c] ++ [Choice c b' | b' <- shrink b]
  shrink (Notify o) = Notify <$> shrink o

localJsonRoundtripSerialization :: TypeId -> JSON.Value -> SerializationResponse JSON.Value
localJsonRoundtripSerialization t@(TypeId name proxy) v = case fromTypeName name of
      Nothing -> UnknownType t
      (Just _) -> roundtrip proxy
    where
    roundtrip :: forall a. ToJSON a => FromJSON a => Proxy a -> SerializationResponse JSON.Value
    roundtrip _  = case JSON.fromJSON v :: Result a of
            Error str -> SerializationError str
            Success c ->  SerializationSuccess $ JSON.toJSON c
