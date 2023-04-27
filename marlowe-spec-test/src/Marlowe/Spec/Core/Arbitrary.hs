{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.Core.Arbitrary
  ( arbitraryChoiceName,
    arbitraryFibonacci,
    arbitraryInteger,
    arbitraryNonnegativeInteger,
    arbitraryPositiveInteger,
    arbitraryTimeInterval,
    arbitraryTimeIntervalAfter,
    arbitraryTimeIntervalBefore,
    arbitraryTimeIntervalAround,
    arbitraryTransaction,
    arbitraryValidTransactions,
    chooseArithInt,
  )
where

import qualified Arith
import Data.List (nub)
import Marlowe.Spec.TypeId ()
import Orderings (Ord (..), max)
import Semantics
  ( computeTransaction,
    evalValue,
  )
import SemanticsTypes
  ( Action (..),
    Bound (..),
    Case (..),
    Contract (..),
    Environment_ext (..),
    Input (..),
    IntervalError (..),
    State_ext (..),
    ValueId (..),
    TransactionError (..),
    TransactionOutput (..),
    TransactionOutputRecord_ext (..),
    Transaction_ext (..),
    minTime,
  )
import Test.QuickCheck (Gen, frequency, suchThat, oneof)
import Test.QuickCheck.Arbitrary (Arbitrary (..))
import qualified Test.QuickCheck.Gen as QC (chooseInteger, elements)

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
chooseArithInt :: (Arith.Int, Arith.Int) -> Gen Arith.Int
chooseArithInt (Arith.Int_of_integer i, Arith.Int_of_integer j) =
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
    duration <- chooseArithInt (0, upper - start - 1)
    pure (start, start + duration)

-- | Generate a semi-random time interval after a given time.
arbitraryTimeIntervalAfter :: Arith.Int -> Gen (Arith.Int, Arith.Int)
arbitraryTimeIntervalAfter lower =
  do
    start <- arbitraryNonnegativeInteger `suchThat` less_eq lower
    duration <- arbitraryNonnegativeInteger
    pure (start, start + duration)

greater_eq :: Orderings.Ord a => a -> a -> Bool
greater_eq = flip less_eq

-- | Generate a random step for a contract.
arbitraryTransaction :: State_ext ()             -- ^ The state of the contract.
                     -> Contract                 -- ^ The contract.
                     -> Gen (Transaction_ext ()) -- ^ Generator for a transaction input for a single step.
arbitraryTransaction _ (When [] timeout _) = Transaction_ext <$> arbitraryTimeIntervalAfter timeout <*> pure [] <*> pure ()
arbitraryTransaction state (When cases timeout _) =
  do
    let
      isEmptyChoice (Choice _ []) = True
      isEmptyChoice _             = False
      minTime' = minTime state

    isTimeout <- frequency [(9, pure False), (1, pure True)]
    if isTimeout || less_eq timeout minTime' || all (isEmptyChoice . getAction) cases
      then Transaction_ext <$> arbitraryTimeIntervalAfter timeout <*> pure [] <*> pure ()
      else
        do
          times <- arbitraryTimeIntervalBefore minTime' timeout
          Case action cont <- QC.elements $ filter (not . isEmptyChoice . getAction) cases
          i <- case action of
                 Deposit a p t v -> pure . IDeposit a p t $ evalValue (Environment_ext times ()) state v
                 Choice n bs     -> do
                                      Bound lower upper <- QC.elements bs
                                      IChoice n <$> chooseArithInt (lower, upper)
                 Notify _        -> pure INotify
          case cont of
            Close -> pure $ Transaction_ext times [i] ()
            _ -> do Transaction_ext _ inps _ <- arbitraryTransaction state cont
                    pure $ Transaction_ext times (i:inps) ()
  where
    getAction :: Case -> Action
    getAction (Case a _) = a
arbitraryTransaction state contract =
  let nextTimeout Close = minTime state
      nextTimeout (Pay _ _ _ _ continuation) = nextTimeout continuation
      nextTimeout (If _ thenContinuation elseContinuation) = maximum' $ nextTimeout <$> [thenContinuation, elseContinuation]
      nextTimeout (When _ timeout _) = timeout
      nextTimeout (Let _ _ continuation) = nextTimeout continuation
      nextTimeout (Assert _ continuation) = nextTimeout continuation
   in Transaction_ext <$> arbitraryTimeIntervalAfter (maximum' [minTime state, nextTimeout contract]) <*> pure [] <*> pure ()
  where
    maximum' = foldl1 Orderings.max

-- | Generate a random path through a contract.
arbitraryValidTransactions :: State_ext ()             -- ^ The state of the contract.
                           -> Contract                 -- ^ The contract.
                           -> Gen [Transaction_ext ()] -- ^ Generator for a transaction inputs.
arbitraryValidTransactions _ Close = pure []
arbitraryValidTransactions state contract =
  do
    txIn <- arbitraryTransaction state contract
    case computeTransaction txIn state contract of -- FIXME: It is tautological to use `computeTransaction` to filter test cases.
      TransactionError _ -> pure []
      TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _) -> (txIn :) <$> arbitraryValidTransactions txOutState txOutContract

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

-- | Generate a time interval.
genInterval :: Gen (Arith.Int, Arith.Int)
genInterval = do
  lower <- arbitraryNonnegativeInteger
  extent <- arbitraryNonnegativeInteger
  pure (lower, lower + extent)

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
  arbitrary = do
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

instance Arbitrary TransactionError where
  arbitrary = oneof
    [ pure TEAmbiguousTimeIntervalError
    , pure TEApplyNoMatchError
    , TEIntervalError <$> arbitrary
    , pure TEUselessTransaction
    ]

  shrink (TEIntervalError i) = [TEIntervalError i' | i' <- shrink i]
  shrink _ = []

instance Arbitrary IntervalError where
  arbitrary = do
    lower <- arbitraryInteger
    extent <- arbitraryNonnegativeInteger
    oneof
      [ pure $ InvalidInterval (lower, lower + extent)
      , IntervalInPastError <$> arbitraryNonnegativeInteger <*> pure  (lower, lower + extent)
      ]

  shrink (InvalidInterval i) = InvalidInterval <$> shrinkTimeInterval i
  shrink (IntervalInPastError e i) = IntervalInPastError <$> shrink e <*> shrinkTimeInterval i

instance Arbitrary (Environment_ext ()) where
  arbitrary = Environment_ext <$> genInterval <*> pure ()
  shrink (Environment_ext i ()) = Environment_ext <$> shrinkTimeInterval i <*> pure ()
