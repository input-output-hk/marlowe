{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Marlowe.Spec.Core.Arbitrary where

import qualified Arith
import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Control.Monad (liftM2)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import Data.Data (Proxy (..))
import Data.List (nub)
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), parseValidResponse)
import Marlowe.Spec.TypeId (TypeId (..))
import Orderings (Ord (..), max)
import QuickCheck.GenT (GenT, MonadGen (..), frequency, resize, scale, sized, suchThat, vectorOf)
import Semantics (Payment (..), TransactionError (..), TransactionOutput (..), TransactionOutputRecord_ext (..), TransactionWarning (..), Transaction_ext (..), computeTransaction, evalValue)
import SemanticsGuarantees (valid_state)
import SemanticsTypes (Action (..), Bound (..), Case (..), ChoiceId (ChoiceId), Contract (..), Environment_ext (..), Input (..), IntervalError (..), Observation (..), Party, Payee (..), State_ext (..), Token (..), Value (..), ValueId (..), minTime)
import Test.QuickCheck (Gen, chooseInt, getSize)
import Test.QuickCheck.Arbitrary (Arbitrary (..))
import Test.QuickCheck.Gen (chooseInteger, elements)

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

data GenerateRandomValueException = GenerateRandomValueException String
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
  (\candidate -> length (f candidate) > 0 && length (f candidate) < length (f selected)) universe

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

chooseInteger' :: (Arith.Int, Arith.Int) -> Gen Arith.Int
chooseInteger' (Arith.Int_of_integer i, Arith.Int_of_integer j) =
  Arith.Int_of_integer <$> chooseInteger (i, j)

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

type TimeInterval = (Arith.Int, Arith.Int)

-- | Geneate a semi-random time interval.
arbitraryTimeInterval :: Gen TimeInterval
arbitraryTimeInterval =
  do
    start <- arbitraryInteger
    duration <- arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Generate a semi-random time interrval straddling a given time.
arbitraryTimeIntervalAround :: Arith.Int -> Gen TimeInterval
arbitraryTimeIntervalAround limit =
  do
    start <- arbitraryInteger `suchThat` (less_eq limit)
    duration <- ((limit - start) +) <$> arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Generate a semi-random time interval before a given time.
arbitraryTimeIntervalBefore :: Arith.Int -> Arith.Int -> Gen TimeInterval
arbitraryTimeIntervalBefore lower upper =
  do
    start <- arbitraryInteger `suchThat` (less_eq lower)
    duration <- chooseInteger' (0, upper - start - 1)
    pure (start, start + duration)

-- | Generate a semi-random time interval after a given time.
arbitraryTimeIntervalAfter :: Arith.Int -> Gen TimeInterval
arbitraryTimeIntervalAfter lower =
  do
    start <- arbitraryInteger `suchThat` (\t -> less t lower)
    duration <- arbitraryNonnegativeInteger
    pure (start, start + duration)

-- | Shrink a generated time interval.
shrinkTimeInterval :: TimeInterval -> [TimeInterval]
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


arbitrarySeed :: Gen Int
arbitrarySeed = resize 10000 $ choose (1, 10000000)

genToken :: InterpretJsonRequest -> GenT IO Token
genToken interpret = do
  size <- liftGen $ getSize
  seed <- liftGen $ arbitrarySeed
  liftIO do
    res <- interpret (GenerateRandomValue (TypeId "Core.Token" (Proxy :: Proxy Token)) size seed)
    case parseValidResponse res of
      Left err -> throwIO $ GenerateRandomValueException err
      Right (UnknownType _) -> throwIO $ GenerateRandomValueException "Client process doesn't know how to generate Core.Token"
      Right (RandomValue t) -> pure t

genParty :: InterpretJsonRequest -> GenT IO Party
genParty interpret = do
  size <- liftGen $ getSize
  seed <- liftGen $ arbitrarySeed
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

-- | Some value identifiers.
randomValueIds :: [ValueId]
randomValueIds = ValueId <$>
  [
    "x"
  , "id"
  , "lab"
  , "idea"
  , "story"
  , "memory"
  , "fishing"
  , ""
  , "drawing"
  , "reaction"
  , "difference"
  , "replacement"
  , "paper apartment"
  , "leadership information"
  , "entertainment region assumptions"
  , "candidate apartment reaction replacement"  -- NB: Too long for ledger.
  ]

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
            [ ( 8, resize (n - 2) $ genAndObs)
            , ( 8, resize (n - 2) $ genOrObs)
            , ( 8, resize (n - 1) $ genNotObs)
            , (16, genChoseSomething)
            , ( 8, resize (n - 2) $ genValueGE)
            , ( 8, resize (n - 2) $ genValueGT)
            , ( 8, resize (n - 2) $ genValueLT)
            , ( 8, resize (n - 2) $ genValueLE)
            , ( 8, resize (n - 2) $ genValueEQ)
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
      [ (4, Deposit <$> genParty i <*> genParty i <*> genToken i <*> genValue i)
      , (5, do
          lSize <- liftGen $ chooseInt (1, 4)
          Choice <$> genChoiceId i <*> vectorOf lSize (liftGen genBound)
        )
      , (1, Notify <$> genObservation i)
      ]

genCase :: InterpretJsonRequest -> GenT IO Case
genCase i = Case <$> genAction i <*> genContract i

genContract :: InterpretJsonRequest -> GenT IO Contract
genContract i = sized (
  \case n | n <= 1 -> genClose
          | otherwise -> frequency
            [ ( 30, genClose)
            , ( 20, genPay n)
            , ( 15, genIf n)
            , ( 20, genWhen n)
            , ( 10, genLet n)
            , ( 5, genAssert n)
            ]
  )
  where
  genClose = pure Close
  genPay n = Pay <$> genParty i <*> genPayee i <*> genToken i <*> limit (genValue i) <*> resize (n - 1) (genContract i)
  genIf n = If <$> limit  (genObservation i) <*> resize (n - 1) (genContract i) <*> resize (n - 1) (genContract i)
  genWhen n = do
    lSize <- liftGen $ chooseInt (0, 3)
    cases <- vectorOf lSize (resize (n - lSize) (genCase i))
    timeout <- liftGen $ arbitraryInteger
    cont <- resize (n - 1) (genContract i)
    pure $ When cases timeout cont
  genLet n = Let <$> liftGen genValueId <*> limit (genValue i) <*> resize (n - 1) (genContract i)
  genAssert n = Assert <$> limit (genObservation i) <*> resize (n - 1) (genContract i)
  limit = scale (min 3)

genInput :: InterpretJsonRequest -> GenT IO Input
genInput i = frequency
  [ (50, IDeposit <$> genParty i <*> genParty i <*> genToken i <*> liftGen arbitraryInteger)
  , (45, IChoice <$> genChoiceId i <*> liftGen arbitraryInteger )
  , (5, pure INotify)
  ]

genTransaction :: InterpretJsonRequest -> GenT IO (Transaction_ext ())
genTransaction i = do
  lower <- liftGen $ arbitraryInteger
  extent <- liftGen $ arbitraryNonnegativeInteger
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
    , (70, do
              wSize <- liftGen $ chooseInt (0, 2)
              warnings <- vectorOf wSize $ genTransactionWarning i
              pSize <- liftGen $ chooseInt (0, 2)
              payments <- vectorOf pSize $ genPayment i
              state <- resize 2 $ genState i
              contract <- resize 2 $ genContract i
              pure $ TransactionOutput $ TransactionOutputRecord_ext warnings payments state contract ()
      )
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
      else do
             times <- arbitraryTimeIntervalBefore minTime' timeout
             case' <- elements $ filter (not . isEmptyChoice . getAction) cases
             i <- case getAction case' of
                    Deposit a p t v -> pure . IDeposit a p t $ evalValue (Environment_ext times ()) state v
                    Choice n bs     -> do
                                         Bound lower upper <- elements bs
                                         IChoice n <$> chooseInteger' (lower, upper)
                    Notify _        -> pure INotify
             pure $ Transaction_ext times [i] ()
  where
    getAction :: Case -> Action
    getAction (Case a _) = a

arbitraryValidStep state contract =
{-
  NOTE: Alternatively, if semantics should allow applying `[]` to a non-quiescent contract
  without ever throwing a timeout-related error, then replace the above with the following:

  TransactionInput <$> arbitraryTimeIntervalAround minTime <*> pure []
-}
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

-- | Generate random transaction input.
arbitraryValidInput :: State_ext ()             -- ^ The state of the contract.
                    -> Contract                 -- ^ The contract.
                    -> Gen (Transaction_ext ()) -- ^ Generator for a transaction input.
arbitraryValidInput = arbitraryValidInput' Nothing

arbitraryValidInput' :: Maybe (Transaction_ext ()) -> State_ext () -> Contract -> Gen (Transaction_ext ())
arbitraryValidInput' Nothing state contract = arbitraryValidStep state contract
arbitraryValidInput' (Just tr@(Transaction_ext timeInterval input _)) state contract =
  case computeTransaction tr state contract of
    TransactionError _              -> pure tr
    TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _) -> do
                               Transaction_ext a nextInput b <- arbitraryValidStep state contract
                               let
                                 combinedInput = input ++ nextInput -- {txInputs = txInputs input ++ txInputs nextInput}
                                 newTr = Transaction_ext a combinedInput b
                               case computeTransaction newTr txOutState txOutContract of
                                 TransactionError _                                        -> pure tr
                                 TransactionOutput (TransactionOutputRecord_ext _ _ _ _ _) -> pure newTr

-- | Generate a random path through a contract.
arbitraryValidInputs :: State_ext ()             -- ^ The state of the contract.
                     -> Contract                 -- ^ The contract.
                     -> Gen [Transaction_ext ()] -- ^ Generator for a transaction inputs.
arbitraryValidInputs _ Close = pure []
arbitraryValidInputs state contract =
  do
    input <- arbitraryValidInput state contract
    case computeTransaction input state contract of  -- FIXME: It is tautological to use `computeTransaction` to filter test cases.
      TransactionError _ -> pure []
      TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _) -> (input :) <$> arbitraryValidInputs txOutState txOutContract
