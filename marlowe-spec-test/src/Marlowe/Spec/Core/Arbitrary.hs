{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.Core.Arbitrary
  where

import qualified Arith
import Data.List (nub)
import Marlowe.Spec.TypeId (TypeId (..))
import Orderings (Ord (..))
import Semantics (TransactionError (..))
import SemanticsTypes
  ( Action (..),
    Bound (..),
    ChoiceId (..),
    Environment_ext (..),
    Observation (..),
    Party (..),
    Payee (..),
    Token (..),
    Value (..),
    ValueId (..),
    IntervalError (..),
  )
import Test.QuickCheck (Gen)
import Test.QuickCheck.Arbitrary (Arbitrary (..))
import QuickCheck.GenT (MonadGen (..), frequency, resize, sized, suchThat)
import qualified Test.QuickCheck.Gen as QC (chooseInteger)

-- | Part of the Fibonacci sequence.
fibonaccis :: Num a => [a]
fibonaccis = [2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584]

-- | Inverse-Fibanoncci frequencies.
fibonacciFrequencies :: Integral a => [a]
fibonacciFrequencies = (1000000 `div`) <$> fibonaccis

-- | Select an element of a list with propability proportional to inverse-Fibonacci weights.
arbitraryFibonacci :: [a] -> Gen a
arbitraryFibonacci = frequency . zip fibonacciFrequencies . fmap pure

-- | Shrink a string.
shrinkString :: (a -> String) -> [a] -> a -> [a]
shrinkString f universe selected = filter
  (\candidate -> not (null (f candidate)) && length (f candidate) < length (f selected)) universe

-- | An arbitrary integer, mostly small.
arbitraryInteger :: Gen Arith.Int
arbitraryInteger = Arith.Int_of_integer <$>
  frequency
    [
      ( 5, arbitrary `suchThat` (< 0))
    , (30, arbitrary `suchThat` (> 0))
    , ( 5, pure 0)
    , (60, arbitraryFibonacci fibonaccis)
    ]

-- | An arbitrary integer within an interval.
chooseinteger :: (Arith.Int, Arith.Int) -> Gen Arith.Int
chooseinteger (Arith.Int_of_integer i, Arith.Int_of_integer j) =
  Arith.Int_of_integer <$> QC.chooseInteger (i, j)

-- | An arbitrary non-negative integer, mostly small.
arbitraryNonnegativeInteger :: Gen Arith.Int
arbitraryNonnegativeInteger = Arith.Int_of_integer <$>
  frequency
    [
      (60, arbitrary `suchThat` (>= 0))
    , (30, arbitraryFibonacci fibonaccis)
    ]

-- | An arbitrary positive integer, mostly small.
arbitraryPositiveInteger :: Gen Arith.Int
arbitraryPositiveInteger = Arith.Int_of_integer <$>
  frequency
    [
      (60, arbitrary `suchThat` (> 0))
    , (30, arbitraryFibonacci fibonaccis)
    ]

-- | Geneate a semi-random time interval.
arbitraryTimeInterval :: Gen (Arith.Int, Arith.Int)
arbitraryTimeInterval =
  do
    start <- arbitraryNonnegativeInteger
    duration <- arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Generate a semi-random time interrval straddling a given time.
arbitraryTimeIntervalAround :: Arith.Int -> Gen (Arith.Int, Arith.Int)
arbitraryTimeIntervalAround limit =
  do
    start <- arbitraryNonnegativeInteger `suchThat` greater_eq limit
    duration <- ((limit - start) +) <$> arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Generate a semi-random time interval before a given time.
arbitraryTimeIntervalBefore :: Arith.Int -> Arith.Int -> Gen (Arith.Int, Arith.Int)
arbitraryTimeIntervalBefore lower upper =
  do
    start <- arbitraryNonnegativeInteger `suchThat` greater_eq lower
    duration <- chooseinteger (0, upper - start - 1)
    pure (start, start + duration)

-- | Generate a semi-random time interval after a given time.
arbitraryTimeIntervalAfter :: Arith.Int -> Gen (Arith.Int, Arith.Int)
arbitraryTimeIntervalAfter lower =
  do
    start <- arbitraryNonnegativeInteger `suchThat` less_eq lower
    duration <- arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Shrink a generated time interval.
shrinkTimeInterval :: (Arith.Int, Arith.Int) -> [(Arith.Int, Arith.Int)]
shrinkTimeInterval (start, end) =
  let
    mid = (start + end) `Arith.divide_int` 2
  in
    filter (/= (start, end))
      $ nub
      [
        (start, start)
      , (start, mid  )
      , (mid  , mid  )
      , (mid  , end  )
      , (end  , end  )
      ]

greater_eq :: Orderings.Ord a => a -> a -> Bool
greater_eq = flip less_eq

-- | Some choice names.
randomChoiceNames :: [String]
randomChoiceNames =
  [
    "be"
  , "dry"
  , "grab"
  , "weigh"
  , "enable"
  , "enhance"
  , "allocate"
  , ""
  , "originate"
  , "characterize"
  , "derive witness"
  , "envisage software"
  , "attend unknown animals"
  , "position increated radiation"
  , "proclaim endless sordid figments"
  , "understand weigh originate envisage"  -- NB: Too long for ledger.
  ]

-- | Generate a choice name from a few possibilities.
arbitraryChoiceName :: Gen String
arbitraryChoiceName = arbitraryFibonacci randomChoiceNames

-- | Shrink a generated choice name
shrinkChoiceName :: String -> [String]
shrinkChoiceName = shrinkString id randomChoiceNames

genValueId :: Gen ValueId
genValueId = arbitraryFibonacci randomValueIds

genBound :: Gen Bound
genBound = do
  lower <- arbitraryInteger
  extent <- arbitraryNonnegativeInteger
  pure $ Bound lower (lower + extent)

genInterval :: Gen (Arith.Int, Arith.Int)
genInterval = do
  lower <- arbitraryNonnegativeInteger
  extent <- arbitraryNonnegativeInteger
  pure (lower, lower + extent)

genIntervalError :: Gen IntervalError
genIntervalError = do
  lower <- arbitraryInteger
  extent <- arbitraryNonnegativeInteger
  frequency
    [ (1, pure $ InvalidInterval (lower, lower + extent))
    , (1, IntervalInPastError <$> liftGen arbitraryNonnegativeInteger <*> pure  (lower, lower + extent) )
    ]

genTransactionError :: Gen TransactionError
genTransactionError = frequency
    [ (1, pure TEAmbiguousTimeIntervalError)
    , (1, pure TEApplyNoMatchError)
    , (1, TEIntervalError <$> genIntervalError)
    , (1, pure TEUselessTransaction)
    ]

genEnvironment :: Gen (Environment_ext ())
genEnvironment = Environment_ext <$> genInterval <*> pure ()

-- | Some value identifiers.
randomValueIds :: [ValueId]
randomValueIds =
  [
    ValueId "x"
  , ValueId "id"
  , ValueId "lab"
  , ValueId "idea"
  , ValueId "story"
  , ValueId "memory"
  , ValueId "fishing"
  , ValueId ""
  , ValueId "drawing"
  , ValueId "reaction"
  , ValueId "difference"
  , ValueId "replacement"
  , ValueId "paper apartment"
  , ValueId "leadership information"
  , ValueId "entertainment region assumptions"
  , ValueId "candidate apartment reaction replacement"  -- NB: Too long for ledger.
  ]

instance Arbitrary Arith.Int where
  arbitrary = arbitraryInteger

instance Arbitrary ValueId where
  arbitrary = arbitraryFibonacci randomValueIds
  shrink = shrinkString (\(ValueId x) -> x) randomValueIds

instance Arbitrary Bound where
  arbitrary =
    do
      lower <- arbitraryInteger
      extent <- arbitraryNonnegativeInteger
      pure $ Bound lower (lower + extent)
  shrink (Bound lower upper) =
    let
      mid = (lower + upper) `Arith.divide_int` 2
    in
      filter (/= Bound lower upper)
        $ nub
        [
          Bound lower lower
        , Bound lower mid
        , Bound mid   mid
        , Bound mid   upper
        , Bound upper upper
        ]

instance Arbitrary Token where
  arbitrary =
     do
       isAda <- arbitrary
       if isAda
         then pure $ Token "" ""
         else Token <$> arbitrary <*> arbitrary
  shrink (Token c n)
    | c == "" && n == "" = []
    | otherwise          = Token "" "" : [Token c' n' | c' <- shrink c, n' <- shrink n]

instance Arbitrary Party where
  arbitrary =
    do
       isPubKeyHash <- frequency [(2, pure True), (8, pure False)]
       if isPubKeyHash
         then Address <$> arbitrary
         else Role <$> arbitraryFibonacci randomRoleNames
  shrink (Address _) = Role <$> randomRoleNames
  shrink (Role _)    = Role <$> randomRoleNames

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
