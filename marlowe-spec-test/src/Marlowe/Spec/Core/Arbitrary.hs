{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Marlowe.Spec.Core.Arbitrary
  ( genValue
  , genObservation
  , genToken
  , genParty
  , genPayee
  , genChoiceId
  , genBound
  , genState
  , genEnvironment
  , genContract
  , genGoldenContract
  , genInterval
  , genTransaction
  , genAction
  , genInput
  , genPayment
  , genTransactionWarning
  , genIntervalError
  , genTransactionError
  , genTransactionOutput
  , arbitraryValidInputs
  , arbitraryValidStep
  , arbitraryNonnegativeInteger
  , arbitraryFibonacci
  , arbitraryPositiveInteger
  , arbitraryChoiceName
  , arbitraryTimeInterval
  , arbitraryTimeIntervalAfter
  , arbitraryTimeIntervalBefore
  , arbitraryTimeIntervalAround
  , shrinkChoiceName
  , shrinkTimeInterval
  , RandomResponse (..)
  , greater_eq
  )
  where

import Arith (divide_int)
import qualified Arith
import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Control.Monad (liftM2)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import Data.Data (Proxy (..))
import Data.Function (on)
import Data.List (nub, nubBy)
import Data.Map (Map, fromList)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import Marlowe.Spec.TypeId (TypeId (..))
import Orderings (Ord (..), max)
import QuickCheck.GenT (GenT, MonadGen (..), frequency, resize, sized, suchThat, vectorOf)
import Semantics
  ( Payment (..),
    TransactionError (..),
    TransactionOutput (..),
    TransactionOutputRecord_ext (..),
    TransactionWarning (..),
    Transaction_ext (..),
    computeTransaction,
    evalValue,
  )
import SemanticsGuarantees (valid_state)
import SemanticsTypes
  ( Action (..),
    Bound (..),
    Case (..),
    ChoiceId (..),
    Contract (..),
    Environment_ext (..),
    Input (..),
    IntervalError (..),
    Observation (..),
    Party (..),
    Payee (..),
    State_ext (..),
    Token (..),
    Value (..),
    ValueId (..),
    minTime,
  )
import Test.QuickCheck (Gen, chooseInt, elements, getSize)
import Test.QuickCheck.Arbitrary (Arbitrary (..), shrinkList)
import Test.QuickCheck.Gen (listOf)
import qualified Test.QuickCheck.Gen as QC (chooseInteger, elements)
import qualified Examples.Escrow as Escrow
import qualified Examples.Swap as Swap

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
    start <- arbitraryInteger
    duration <- arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Generate a semi-random time interrval straddling a given time.
arbitraryTimeIntervalAround :: Arith.Int -> Gen (Arith.Int, Arith.Int)
arbitraryTimeIntervalAround limit =
  do
    start <- arbitraryInteger `suchThat` greater_eq limit
    duration <- ((limit - start) +) <$> arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Generate a semi-random time interval before a given time.
arbitraryTimeIntervalBefore :: Arith.Int -> Arith.Int -> Gen (Arith.Int, Arith.Int)
arbitraryTimeIntervalBefore lower upper =
  do
    start <- arbitraryInteger `suchThat` greater_eq lower
    duration <- chooseinteger (0, upper - start - 1)
    pure (start, start + duration)

-- | Generate a semi-random time interval after a given time.
arbitraryTimeIntervalAfter :: Arith.Int -> Gen (Arith.Int, Arith.Int)
arbitraryTimeIntervalAfter lower =
  do
    start <- arbitraryInteger `suchThat` less_eq lower
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

genContract :: InterpretJsonRequest -> GenT IO Contract
genContract interpret = frequency [(90, gen =<< liftGen arbitrary), (10, genGoldenContract interpret)]
  where gen context = sized \size -> arbitraryContractSized (min (size `div` 6) 5) context interpret -- Keep tests from growing too large to execute by capping the maximum contract depth at 5 (default size is 30)

genGoldenContract :: InterpretJsonRequest -> GenT IO Contract
genGoldenContract interpret =
  frequency
    [ (50, escrow),
      (50, swap)
    ]
  where
    escrow :: GenT IO Contract
    escrow = do
      paymentDeadline <- liftGen arbitraryPositiveInteger
      complaintDeadline <- (+ paymentDeadline) <$> liftGen arbitraryPositiveInteger
      disputeDeadline <- (+ complaintDeadline) <$> liftGen arbitraryPositiveInteger
      mediationDeadline <- (+ disputeDeadline) <$> liftGen arbitraryPositiveInteger
      let args =
            Escrow.EscrowArgs_ext
              <$> genValue interpret
              <*> genToken interpret
              <*> genParty interpret
              <*> genParty interpret
              <*> genParty interpret
              <*> pure paymentDeadline
              <*> pure complaintDeadline
              <*> pure disputeDeadline
              <*> pure mediationDeadline
              <*> pure ()
      Escrow.escrow <$> args

    swap :: GenT IO Contract
    swap = do
      let p1 =
            Swap.SwapParty_ext
              <$> genParty interpret
              <*> genValue interpret
              <*> genToken interpret
              <*> liftGen arbitraryPositiveInteger
              <*> pure ()
          p2 =
            Swap.SwapParty_ext
              <$> genParty interpret
              <*> genValue interpret
              <*> genToken interpret
              <*> liftGen arbitraryPositiveInteger
              <*> pure ()
      Swap.swap <$> p1 <*> p2

genPayee ::  InterpretJsonRequest -> GenT IO Payee
genPayee i = do
  isParty <- liftGen arbitrary
  if isParty
    then Party <$> genParty i
    else Account <$> genParty i

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

genChoiceId :: InterpretJsonRequest -> GenT IO ChoiceId
genChoiceId i = ChoiceId <$> liftGen arbitraryChoiceName <*> genParty i

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
  genUseValue = UseValue <$> liftGen genValueId
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
          Choice <$> genChoiceId i <*> vectorOf lSize (liftGen genBound)
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
      bounds <- vectorOf boundSize (liftGen genValueId >*< liftGen arbitraryInteger)
      minTime' <- liftGen arbitraryNonnegativeInteger
      pure $ State_ext accounts choices bounds minTime' ()
    )

genTransactionWarning :: InterpretJsonRequest -> GenT IO TransactionWarning
genTransactionWarning i = frequency
  [ ( 30, TransactionNonPositiveDeposit <$> genParty i <*> genParty i <*> genToken i <*> liftGen arbitraryInteger)
  , ( 30, TransactionNonPositivePay <$> genParty i <*> genPayee i <*> genToken i <*> liftGen arbitraryInteger)
  , ( 30, TransactionShadowing <$> liftGen genValueId <*> liftGen arbitraryInteger <*> liftGen arbitraryInteger)
  , ( 10, pure TransactionAssertionFailed)
  ]

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

genTransactionOutput :: InterpretJsonRequest -> GenT IO TransactionOutput
genTransactionOutput i =
 frequency
    [ (30, TransactionError <$> liftGen genTransactionError)
    , (70, TransactionOutput <$> do
                                   wSize <- liftGen $ chooseInt (0, 2)
                                   warnings <- vectorOf wSize $ genTransactionWarning i
                                   pSize <- liftGen $ chooseInt (0, 2)
                                   payments <- vectorOf pSize $ genPayment i
                                   state <- resize 2 $ genState i
                                   contract <- resize 2 $ genContract i
                                   pure $ TransactionOutputRecord_ext warnings payments state contract ())
    ]

genEnvironment :: Gen (Environment_ext ())
genEnvironment = Environment_ext <$> genInterval <*> pure ()

-- | Generate a random step for a contract.
arbitraryValidStep :: State_ext ()             -- ^ The state of the contract.
                   -> Contract                 -- ^ The contract.
                   -> Gen (Transaction_ext ()) -- ^ Generator for a transaction input for a single step.
arbitraryValidStep _ (When [] timeout _) = Transaction_ext <$> arbitraryTimeIntervalAfter timeout <*> pure [] <*> pure ()
arbitraryValidStep state (When cases timeout _) =
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
            _ -> do Transaction_ext _ inputs _ <- arbitraryValidStep state cont
                    pure $ Transaction_ext times (i:inputs) ()
  where
    getAction :: Case -> Action
    getAction (Case a _) = a

arbitraryValidStep state contract =
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
arbitraryValidInputs :: State_ext ()             -- ^ The state of the contract.
                     -> Contract                 -- ^ The contract.
                     -> Gen [Transaction_ext ()] -- ^ Generator for a transaction inputs.
arbitraryValidInputs _ Close = pure []
arbitraryValidInputs state contract =
  do
    txIn <- arbitraryValidStep state contract
    case computeTransaction txIn state contract of  -- FIXME: It is tautological to use `computeTransaction` to filter test cases.
      TransactionError _ -> pure []
      TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _) -> (txIn :) <$> arbitraryValidInputs txOutState txOutContract

-- | Generate a random case, weighted towards different contract constructs.
arbitraryCaseWeighted :: [(Int, Int, Int, Int, Int, Int)] -- ^ The weights for contract terms.
                      -> Context                          -- ^ The Marlowe context.
                      -> InterpretJsonRequest             -- ^ The JSON request interpreter.
                      -> GenT IO Case                     -- ^ Generator for a case.
arbitraryCaseWeighted w context interpret =
  Case <$> genAction interpret <*> arbitraryContractWeighted w context interpret

-- | Generate an arbitrary contract, weighted towards different contract constructs.
arbitraryContractWeighted :: [(Int, Int, Int, Int, Int, Int)] -- ^ The weights of contract terms, which must eventually include `Close` as a posibility.
                          -> Context                          -- ^ The Marlowe context.
                          -> InterpretJsonRequest             -- ^ The JSON request interpreter.
                          -> GenT IO Contract                 -- ^ Generator for a contract.
arbitraryContractWeighted ((wClose, wPay, wIf, wWhen, wLet, wAssert) : w) context interpret =
  frequency
    [
      (wClose , pure Close)
    , (wPay   , Pay <$> genParty interpret <*> genPayee interpret <*> genToken interpret <*> genValue interpret <*> arbitraryContractWeighted w context interpret)
    , (wIf    , If <$> genObservation interpret <*> arbitraryContractWeighted w context interpret <*> arbitraryContractWeighted w context interpret)
    , (wWhen  , When <$> (liftGen (chooseInt (0, length w)) >>= flip vectorOf (arbitraryCaseWeighted w context interpret)) <*> liftSemiArbitrary context <*> arbitraryContractWeighted w context interpret)
    , (wLet   , Let <$> liftSemiArbitrary context <*> genValue interpret <*> arbitraryContractWeighted w context interpret)
    , (wAssert, Assert <$> genObservation interpret <*> arbitraryContractWeighted w context interpret)
    ]
  where
    liftSemiArbitrary :: SemiArbitrary a => Context -> GenT IO a
    liftSemiArbitrary = liftGen . semiArbitrary
arbitraryContractWeighted [] _ _ = pure Close

-- | Default weights for contract terms.
defaultContractWeights :: (Int, Int, Int, Int, Int, Int)
defaultContractWeights = (35, 20, 10, 15, 20, 5)

-- | Generate a semi-random contract of a given depth.
arbitraryContractSized :: Int           -- ^ The maximum depth.
                       -> Context       -- ^ The Marlowe context.
                       -> InterpretJsonRequest
                       -> GenT IO Contract  -- ^ Generator for a contract.
arbitraryContractSized = arbitraryContractWeighted . (`replicate` defaultContractWeights)

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

-- | Class for arbitrary values with respect to a context.
class Arbitrary a => SemiArbitrary a where
  -- | Generate an arbitrary value within a context.
  semiArbitrary :: Context -> Gen a
  semiArbitrary context =
     case fromContext context of
       [] -> arbitrary
       xs -> perturb arbitrary xs
  -- | Report values present in a context.
  fromContext :: Context -> [a]
  fromContext _ = []

-- | Select an element of a list with high probability, or create a non-element at random with low probability.
perturb :: Gen a   -- ^ The generator for a random item.
        -> [a]     -- ^ The list of pre-defined items.
        -> Gen a   -- ^ Generator for an item
perturb gen [] = gen
perturb gen xs = frequency [(20, gen), (80, elements xs)]

-- | Context for generating correlated Marlowe terms and state.
data Context =
  Context
  {
    amounts      :: [Arith.Int]                  -- ^ Universe of token amounts.
  , choiceNames  :: [String]                     -- ^ Universe of choice names.
  , chosenNums   :: [Arith.Int]                  -- ^ Universe of chosen numbers.
  , valueIds     :: [ValueId]                    -- ^ Universe of value identifiers.
  , values       :: [Arith.Int]                  -- ^ Universe of values.
  , times        :: [Arith.Int]                  -- ^ Universe of times.
  , cboundValues :: Map ValueId Arith.Int        -- ^ Bound values for state.
  }

instance Prelude.Ord ValueId where
   compare (ValueId a) (ValueId b) = compare a b

instance Arbitrary Context where
  arbitrary =
    do
      amounts <- listOf arbitraryPositiveInteger
      choiceNames <- listOf arbitraryChoiceName
      chosenNums <- listOf arbitraryInteger
      valueIds <- arbitrary
      values <- listOf arbitraryInteger
      times <- listOf arbitraryPositiveInteger
      cboundValues <- fromList . nubBy ((==) `on` fst) <$> listOf ((,) <$> perturb arbitrary valueIds <*> perturb arbitraryInteger values)
      pure Context{..}
  shrink context@Context{..} =
      [context {amounts = amounts'} | amounts' <- shrink amounts]
      ++ [context {choiceNames = choiceNames'} | choiceNames' <- shrinkList shrinkChoiceName choiceNames]
      ++ [context {chosenNums = chosenNums'} | chosenNums' <- shrink chosenNums]
      ++ [context {valueIds = valueIds'} | valueIds' <- shrink valueIds]
      ++ [context {values = values'} | values' <- shrink values]
      ++ [context {times = times'} | times' <- shrink times]
      ++ [context {cboundValues = cboundValues'} | cboundValues' <- shrink cboundValues]

instance Arbitrary Arith.Int where
  arbitrary = arbitraryInteger

instance SemiArbitrary Arith.Int where
  fromContext = times

instance Arbitrary ValueId where
  arbitrary = arbitraryFibonacci randomValueIds
  shrink = shrinkString (\(ValueId x) -> x) randomValueIds

instance SemiArbitrary ValueId where
  fromContext = valueIds

instance Arbitrary Bound where
  arbitrary =
    do
      lower <- arbitraryInteger
      extent <- arbitraryNonnegativeInteger
      pure $ Bound lower (lower + extent)
  shrink (Bound lower upper) =
    let
      mid = (lower + upper) `divide_int` 2
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

instance SemiArbitrary Bound where
  semiArbitrary context =
      do
        lower <- semiArbitrary context
        extent <- arbitraryNonnegativeInteger
        pure $ Bound lower (lower + extent)

instance SemiArbitrary [Bound] where
  semiArbitrary context = listOf $ semiArbitrary context
