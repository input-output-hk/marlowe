{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.Core.SemiArbitrary
  ( arbitraryContractWeighted
  , arbitraryTransaction
  , arbitraryValidTransactions
  , genContext
  , Context (..)
  , SemiArbitrary (..)
  )
  where

import qualified Arith
import Control.Monad (replicateM)
import Data.Function (on)
import Data.List (nubBy)
import Data.Map (Map, fromList, toList)
import qualified Examples.Escrow as Escrow
import qualified Examples.Swap as Swap
import Marlowe.Spec.Core.Arbitrary
  ( arbitraryChoiceName,
    arbitraryInteger,
    arbitraryNonnegativeInteger,
    arbitraryPositiveInteger,
    arbitraryTimeIntervalAfter,
    arbitraryTimeIntervalBefore,
    chooseinteger,
    genBound,
    genTransactionError,
    genValueId,
  )
import Marlowe.Spec.Core.Generators (genParty, genToken)
import Marlowe.Spec.Interpret
  ( InterpretJsonRequest,
  )
import Orderings (Ord (..), max)
import QuickCheck.GenT
  ( Gen,
    GenT,
    MonadGen (..),
    frequency,
    listOf,
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
    computeTransaction,
    evalValue,
  )
import SemanticsTypes
  ( Action (..),
    Bound (..),
    Case (..),
    ChoiceId (..),
    Contract (..),
    Environment_ext (..),
    Input (..),
    Observation (..),
    Party (..),
    Payee (..),
    State_ext (..),
    Token (..),
    Value (..),
    ValueId (..),
    minTime,
  )
import Test.QuickCheck (chooseInt, elements)
import Test.QuickCheck.Arbitrary (Arbitrary (..))
import qualified Test.QuickCheck.Gen as QC (elements)

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
  {
    parties      :: [Party]                      -- ^ Universe of parties.
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
  }
  deriving Show

genContext :: InterpretJsonRequest -> GenT IO Context
genContext interpret = sized \n ->
  do
    parties <- listOf' n $ genParty interpret
    tokens <- listOf' n $ genToken interpret
    amounts <- liftGen $ listOf' n arbitraryPositiveInteger
    choiceNames <- liftGen $ listOf' n arbitraryChoiceName
    chosenNums <- liftGen $ listOf' n arbitraryInteger
    choiceIds <- listOf' n $ ChoiceId <$> (liftGen $ perturb arbitraryChoiceName choiceNames) <*> perturbM (genParty interpret) parties
    valueIds <- liftGen $ listOf' n genValueId
    values <- liftGen $ listOf' n arbitraryInteger
    times <- liftGen $ listOf' n arbitraryPositiveInteger
    caccounts <- fromList . nubBy ((==) `on` fst) <$> listOf' n ((,) <$> ((,) <$> perturbM (genParty interpret) parties <*> perturbM (genToken interpret) tokens) <*> liftGen (perturb arbitraryPositiveInteger amounts))
    cchoices <- fromList . nubBy ((==) `on` fst) <$> listOf' n ((,) <$> liftGen (elements choiceIds) <*> liftGen (perturb arbitraryInteger chosenNums))
    cboundValues <- fromList . nubBy ((==) `on` fst) <$> listOf' n ((,) <$> liftGen (perturb genValueId valueIds) <*> liftGen (perturb arbitraryInteger values))
    pure Context{..}
  where
    listOf' n gen = choose (1, n) >>= flip replicateM gen

    perturb gen [] = gen
    perturb gen xs = frequency [(20, gen), (80, elements xs)]

    perturbM gen [] = gen
    perturbM gen xs = frequency [(20, gen), (80, liftGen $ elements xs)]

instance Prelude.Ord Party where
  compare (Address a) (Address b) = compare a b
  compare (Address _) (Role _)    = LT
  compare (Role _) (Address _)    = GT
  compare (Role a) (Role b)       = compare a b

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

instance SemiArbitrary Arith.Int where
  fromContext = times

instance SemiArbitrary ValueId where
  fromContext = valueIds

instance SemiArbitrary Bound where
  semiArbitrary context = do
    lower <- semiArbitrary context
    extent <- arbitraryNonnegativeInteger
    pure $ Bound lower (lower + extent)

instance SemiArbitrary [Bound] where
  semiArbitrary context = listOf $ semiArbitrary context

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
    Payment <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> arbitraryInteger

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
  semiArbitrary context = do
    minTime' <- arbitraryNonnegativeInteger
    pure $ State_ext (toList $ caccounts context) (toList $ cchoices context) (toList $ cboundValues context) minTime' ()

instance SemiArbitrary TransactionWarning where
  semiArbitrary context = frequency
    [ ( 30, TransactionNonPositiveDeposit <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> arbitraryInteger)
    , ( 30, TransactionNonPositivePay <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> arbitraryInteger)
    , ( 30, TransactionShadowing <$> semiArbitrary context <*> arbitraryInteger <*> arbitraryInteger)
    , ( 10, pure TransactionAssertionFailed)
    ]

instance SemiArbitrary TransactionOutput where
  semiArbitrary context =
    frequency
       [ (30, TransactionError <$> genTransactionError)
       , (70, TransactionOutput <$> do
                                      wSize <- chooseInt (0, 2)
                                      warnings <- vectorOf wSize $ semiArbitrary context
                                      pSize <- chooseInt (0, 2)
                                      payments <- vectorOf pSize $ semiArbitrary context
                                      state <- resize 2 $ semiArbitrary context
                                      contract <- resize 2 $ semiArbitrary context
                                      pure $ TransactionOutputRecord_ext warnings payments state contract ())
       ]

instance SemiArbitrary (Bool, Contract) where
  semiArbitrary context =
    frequency [(98, (True,) <$> gen), (2, (False,) <$> genGoldenContract context)]
      where gen = sized \size -> arbitraryContractSized (min (size `div` 6) 5) context -- Keep tests from growing too large to execute by capping the maximum contract depth at 5 (default size is 30)

instance SemiArbitrary Contract where
  semiArbitrary context = snd <$> (semiArbitrary context :: Gen (Bool, Contract))

instance SemiArbitrary Action where
  semiArbitrary context = frequency
    [ (7, Deposit <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context)
    , (2, do
        lSize <- chooseInt (1, 4)
        Choice <$> semiArbitrary context <*> vectorOf lSize genBound
      )
    , (1, Notify <$> semiArbitrary context)
    ]

instance SemiArbitrary Input where
  semiArbitrary context = frequency
    [ (50, IDeposit <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> arbitraryInteger)
    , (45, IChoice <$> semiArbitrary context <*> arbitraryInteger )
    , (5, pure INotify)
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
                                      IChoice n <$> chooseinteger (lower, upper)
                 Notify _        -> pure INotify
          case cont of
            Close -> pure $ Transaction_ext times [i] ()
            _ -> do Transaction_ext _ inps _ <- arbitraryTransaction state cont
                    pure $ Transaction_ext times (i:inps) ()
  where
    getAction :: Case -> Action
    getAction (Case a _) = a

arbitraryTransaction state contract =
  let
    nextTimeout Close                                    = minTime state
    nextTimeout (Pay _ _ _ _ continuation)               = nextTimeout continuation
    nextTimeout (If _ thenContinuation elseContinuation) = maximum' $ nextTimeout <$> [thenContinuation, elseContinuation]
    nextTimeout (When _ timeout _)                       = timeout
    nextTimeout (Let _ _ continuation)                   = nextTimeout continuation
    nextTimeout (Assert _ continuation)                  = nextTimeout continuation
  in
    Transaction_ext <$> arbitraryTimeIntervalAfter (maximum' [minTime state, nextTimeout contract]) <*> pure [] <*> pure ()
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
    case computeTransaction txIn state contract of  -- FIXME: It is tautological to use `computeTransaction` to filter test cases.
      TransactionError _ -> pure []
      TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _) -> (txIn :) <$> arbitraryValidTransactions txOutState txOutContract

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
    [
      (wClose , pure Close)
    , (wPay   , Pay <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> arbitraryContractWeighted w context)
    , (wIf    , If <$> semiArbitrary context <*> arbitraryContractWeighted w context <*> arbitraryContractWeighted w context)
    , (wWhen  , When <$> (chooseInt (0, length w) >>= flip vectorOf (arbitraryCaseWeighted w context)) <*> semiArbitrary context <*> arbitraryContractWeighted w context)
    , (wLet   , Let <$> semiArbitrary context <*> semiArbitrary context <*> arbitraryContractWeighted w context)
    , (wAssert, Assert <$> semiArbitrary context <*> arbitraryContractWeighted w context)
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
