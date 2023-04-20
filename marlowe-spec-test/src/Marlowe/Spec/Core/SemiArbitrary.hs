{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.Core.SemiArbitrary
  ( arbitraryCaseWeighted
  , arbitraryContractWeighted
  , arbitraryContractSized
  , Context (..)
  , SemiArbitrary (..)
  )
  where

import qualified Arith
import Data.Map (Map, toList)
import qualified Examples.Escrow as Escrow
import qualified Examples.Swap as Swap
import Marlowe.Spec.Core.Arbitrary
  ( arbitraryInteger,
    arbitraryNonnegativeInteger,
    arbitraryPositiveInteger,
  )
import QuickCheck.GenT
  ( Gen,
    frequency,
    resize,
    sized,
    vectorOf,
  )
import Semantics
  ( Payment (..),
    TransactionOutput (..),
    TransactionOutputRecord_ext (..),
    TransactionWarning (..),
    Transaction_ext (..),
  )
import SemanticsTypes
  ( Action (..),
    Bound (..),
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
    ValueId (..),
  )
import Test.QuickCheck (chooseInt, elements)
import Test.QuickCheck.Arbitrary (Arbitrary (..))

-- | Class for arbitrary values with respect to a context.
class SemiArbitrary a where
  -- | Generate an arbitrary value within a context.
  semiArbitrary :: Context -> Gen a
  semiArbitrary context =
    let xs = fromContext context in elements xs

  -- | Report values present in a context.
  fromContext :: Context -> [a]
  fromContext _ = []

-- | Context for generating correlated Marlowe terms and state.
data Context =
  Context
  { parties      :: [Party]                      -- ^ Universe of parties.
  , tokens       :: [Token]                      -- ^ Universe of tokens.
  , amounts      :: [Arith.Int]                  -- ^ Universe of token amounts.
  , choiceNames  :: [String]                     -- ^ Universe of choice names.
  , chosenNums   :: [Arith.Int]                  -- ^ Universe of chosen numbers.
  , choiceIds    :: [ChoiceId]                   -- ^ Universe of token identifiers.
  , valueIds     :: [ValueId]                    -- ^ Universe of value identifiers.
  , values       :: [Arith.Int]                  -- ^ Universe of values.
  , times        :: [Arith.Int]                  -- ^ Universe of times.
  , caccounts    :: Map (Party, Token) Arith.Int -- ^ Accounts for state.
  , cchoices     :: Map ChoiceId Arith.Int       -- ^ Choices for state.
  , cboundValues :: Map ValueId Arith.Int        -- ^ Bound values for state.
  } deriving Show

instance Prelude.Ord Token where
  compare (Token a1 b1) (Token a2 b2) =
    let res = compare a1 a2
     in case res of
      EQ -> compare b1 b2
      _  -> res

instance Prelude.Ord ChoiceId where
  compare (ChoiceId a1 b1) (ChoiceId a2 b2) =
    let res = compare a1 a2
     in case res of
      EQ -> compare b1 b2
      _  -> res

instance Prelude.Ord ValueId where
  compare (ValueId v1) (ValueId v2) = compare v1 v2

instance Prelude.Ord Party where
  compare (Address a) (Address b) = compare a b
  compare (Address _) (Role _)    = LT
  compare (Role _) (Address _)    = GT
  compare (Role a) (Role b)       = compare a b

instance SemiArbitrary Arith.Int where
  fromContext = times

instance SemiArbitrary ValueId where
  fromContext = valueIds

instance SemiArbitrary Bound where
  semiArbitrary context = do
    lower <- semiArbitrary context
    extent <- arbitraryNonnegativeInteger
    pure $ Bound lower (lower + extent)

instance SemiArbitrary Party where
  fromContext = parties

instance SemiArbitrary Token where
  fromContext = tokens

instance SemiArbitrary ChoiceId where
  fromContext = choiceIds

instance SemiArbitrary Payee where
  semiArbitrary context = do
    isParty <- arbitrary
    if isParty
      then Party <$> semiArbitrary context
      else Account <$> semiArbitrary context

instance SemiArbitrary Payment where
  semiArbitrary context =
    Payment
      <$> semiArbitrary context
      <*> semiArbitrary context
      <*> semiArbitrary context
      <*> arbitraryInteger

instance SemiArbitrary Value where
  semiArbitrary context = sized (
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
      genAvailableMoney = AvailableMoney <$> semiArbitrary context <*> semiArbitrary context
      genConstant = Constant <$> arbitraryInteger
      genNegValue = NegValue <$> semiArbitrary context
      genAddValue = AddValue <$> semiArbitrary context <*> semiArbitrary context
      genSubValue = SubValue <$> semiArbitrary context <*> semiArbitrary context
      genMulValue = MulValue <$> semiArbitrary context <*> semiArbitrary context
      genDivValue = DivValue <$> semiArbitrary context <*> semiArbitrary context
      genChoiceValue = ChoiceValue <$> semiArbitrary context
      genTimeIntervalStart = pure TimeIntervalStart
      genTimeIntervalEnd = pure TimeIntervalEnd
      genUseValue = UseValue <$> semiArbitrary context
      genCond = Cond <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context

instance SemiArbitrary Observation where
  semiArbitrary context = sized (
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
      genAndObs = AndObs <$> semiArbitrary context <*> semiArbitrary context
      genOrObs = OrObs <$> semiArbitrary context <*> semiArbitrary context
      genNotObs = NotObs <$> semiArbitrary context
      genChoseSomething = ChoseSomething <$> semiArbitrary context
      genValueGE = ValueGE <$> semiArbitrary context <*> semiArbitrary context
      genValueGT = ValueGT <$> semiArbitrary context <*> semiArbitrary context
      genValueLT = ValueLT <$> semiArbitrary context <*> semiArbitrary context
      genValueLE = ValueLE <$> semiArbitrary context <*> semiArbitrary context
      genValueEQ = ValueEQ <$> semiArbitrary context <*> semiArbitrary context
      genTrue = pure TrueObs
      genFalse = pure FalseObs

instance SemiArbitrary (State_ext ()) where
  semiArbitrary context =
    pure (State_ext (toList $ caccounts context))
      <*> pure (toList $ cchoices context)
      <*> pure (toList $ cboundValues context)
      <*> arbitraryNonnegativeInteger
      <*> pure ()

instance SemiArbitrary TransactionWarning where
  semiArbitrary context =
    frequency
      [ ( 30,
          TransactionNonPositiveDeposit
            <$> semiArbitrary context
            <*> semiArbitrary context
            <*> semiArbitrary context
            <*> arbitraryInteger
        ),
        ( 30,
          TransactionNonPositivePay
            <$> semiArbitrary context
            <*> semiArbitrary context
            <*> semiArbitrary context
            <*> arbitraryInteger
        ),
        ( 30,
          TransactionShadowing
            <$> semiArbitrary context
            <*> arbitraryInteger
            <*> arbitraryInteger
        ),
        (10, pure TransactionAssertionFailed)
      ]

instance SemiArbitrary TransactionOutput where
  semiArbitrary context =
    frequency
      [ (30, TransactionError <$> arbitrary),
        ( 70,
          TransactionOutput <$> do
            wSize <- chooseInt (0, 2)
            warnings <- vectorOf wSize $ semiArbitrary context
            pSize <- chooseInt (0, 2)
            payments <- vectorOf pSize $ semiArbitrary context
            state <- resize 2 $ semiArbitrary context
            contract <- resize 2 $ semiArbitrary context
            pure $ TransactionOutputRecord_ext warnings payments state contract ()
        )
      ]

instance SemiArbitrary (Bool, Contract) where
  semiArbitrary context =
    frequency [(98, (True,) <$> gen), (2, (False,) <$> genGoldenContract context)]
      where gen = sized \size -> arbitraryContractSized (min (size `div` 6) 5) context -- Keep tests from growing too large to execute by capping the maximum contract depth at 5 (default size is 30)

instance SemiArbitrary Contract where
  semiArbitrary context = snd <$> (semiArbitrary context :: Gen (Bool, Contract))

instance SemiArbitrary Action where
  semiArbitrary context =
    frequency
      [ ( 7,
          Deposit
            <$> semiArbitrary context
            <*> semiArbitrary context
            <*> semiArbitrary context
            <*> semiArbitrary context
        ),
        ( 2,
          do
            lSize <- chooseInt (1, 4)
            Choice
              <$> semiArbitrary context
              <*> vectorOf lSize arbitrary
        ),
        (1, Notify <$> semiArbitrary context)
      ]

instance SemiArbitrary Input where
  semiArbitrary context =
    frequency
      [ ( 50,
          IDeposit
            <$> semiArbitrary context
            <*> semiArbitrary context
            <*> semiArbitrary context
            <*> arbitraryInteger
        ),
        ( 45,
          IChoice
            <$> semiArbitrary context
            <*> arbitraryInteger
        ),
        (5, pure INotify)
      ]

instance SemiArbitrary (Transaction_ext ()) where
  semiArbitrary context = do
    lower <- arbitraryInteger
    extent <- arbitraryNonnegativeInteger
    iSize <- chooseInt (0, 4)
    inps <- vectorOf iSize $ semiArbitrary context
    pure $ Transaction_ext (lower, lower + extent) inps ()

genGoldenContract :: Context -> Gen Contract
genGoldenContract context =
  frequency
    [ (50, escrow),
      (50, swap)
    ]
  where
    escrow :: Gen Contract
    escrow = do
      paymentDeadline <- arbitraryPositiveInteger
      complaintDeadline <- (+ paymentDeadline) <$> arbitraryPositiveInteger
      disputeDeadline <- (+ complaintDeadline) <$> arbitraryPositiveInteger
      mediationDeadline <- (+ disputeDeadline) <$> arbitraryPositiveInteger
      let args =
            Escrow.EscrowArgs_ext
              <$> semiArbitrary context
              <*> semiArbitrary context
              <*> semiArbitrary context
              <*> semiArbitrary context
              <*> semiArbitrary context
              <*> pure paymentDeadline
              <*> pure complaintDeadline
              <*> pure disputeDeadline
              <*> pure mediationDeadline
              <*> pure ()
      Escrow.escrow <$> args

    swap :: Gen Contract
    swap = do
      let p1 =
            Swap.SwapParty_ext
              <$> semiArbitrary context
              <*> semiArbitrary context
              <*> semiArbitrary context
              <*> arbitraryPositiveInteger
              <*> pure ()
          p2 =
            Swap.SwapParty_ext
              <$> semiArbitrary context
              <*> semiArbitrary context
              <*> semiArbitrary context
              <*> arbitraryPositiveInteger
              <*> pure ()
      Swap.swap <$> p1 <*> p2

-- | Generate a random case, weighted towards different contract constructs.
arbitraryCaseWeighted :: [(Int, Int, Int, Int, Int, Int)] -- ^ The weights for contract terms.
                      -> Context                          -- ^ The Marlowe context.
                      -> Gen Case                         -- ^ Generator for a case.
arbitraryCaseWeighted w context =
  Case <$> semiArbitrary context <*> arbitraryContractWeighted w context

-- | Generate an arbitrary contract, weighted towards different contract constructs.
arbitraryContractWeighted :: [(Int, Int, Int, Int, Int, Int)] -- ^ The weights of contract terms, which must eventually include `Close` as a posibility.
                          -> Context                          -- ^ The Marlowe context.
                          -> Gen Contract                     -- ^ Generator for a contract.
arbitraryContractWeighted ((wClose, wPay, wIf, wWhen, wLet, wAssert) : w) context =
  frequency
    [ (wClose, pure Close),
      ( wPay,
        Pay
          <$> semiArbitrary context
          <*> semiArbitrary context
          <*> semiArbitrary context
          <*> semiArbitrary context
          <*> arbitraryContractWeighted w context
      ),
      ( wIf,
        If
          <$> semiArbitrary context
          <*> arbitraryContractWeighted w context
          <*> arbitraryContractWeighted w context
      ),
      ( wWhen,
        When
          <$> (chooseInt (0, length w) >>= flip vectorOf (arbitraryCaseWeighted w context))
          <*> semiArbitrary context
          <*> arbitraryContractWeighted w context
      ),
      ( wLet,
        Let
          <$> semiArbitrary context
          <*> semiArbitrary context
          <*> arbitraryContractWeighted w context
      ),
      ( wAssert,
        Assert
          <$> semiArbitrary context
          <*> arbitraryContractWeighted w context
      )
    ]
arbitraryContractWeighted [] _ = pure Close

-- | Default weights for contract terms.
defaultContractWeights :: (Int, Int, Int, Int, Int, Int)
defaultContractWeights = (25, 20, 10, 30, 20, 5)

-- | Generate a semi-random contract of a given depth.
arbitraryContractSized :: Int           -- ^ The maximum depth.
                       -> Context       -- ^ The Marlowe context.
                       -> Gen Contract  -- ^ Generator for a contract.
arbitraryContractSized = arbitraryContractWeighted . (`replicate` defaultContractWeights)
