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
import Semantics (playTrace, computeTransaction, evalValue, reduceContractUntilQuiescent)
import Marlowe.Spec.TypeId (TypeId (..), fromTypeName)
import Marlowe.Spec.Core.Serialization.Json
import Data.Data (Proxy)
import Data.Aeson (Result (..),FromJSON,ToJSON)
import Data.Map (Map, fromList, keys)
import SemanticsTypes (Token(Token), Party (..), Contract (..), ChoiceId (..), ValueId (..), State_ext (..), Case(..), Action (..), Value (..), Payee (..), Observation (..), Bound (..))
import Test.QuickCheck (Gen, frequency, Arbitrary (..), suchThat, resize)
import qualified Marlowe.Spec.Core.Arbitrary as RandomResponse
import Marlowe.Spec.Core.Arbitrary (arbitraryFibonacci, arbitraryPositiveInteger, arbitraryChoiceName, arbitraryInteger, shrinkChoiceName, shrinkString, arbitraryNonnegativeInteger)
import Test.QuickCheck.Gen (Gen(..))
import Test.QuickCheck.Random (mkQCGen)
import Test.QuickCheck (sized)
import Test.QuickCheck (elements)
import Test.QuickCheck (listOf)
import Test.QuickCheck.Arbitrary (shrinkList)
import qualified Examples.Escrow as Escrow
import qualified Examples.Swap as Swap
import Data.List (nubBy, nub)
import Data.Function (on)
import Arith (divide_int)

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
interpretLocal (GenerateRandomValue t@(TypeId name _) size seed) =
  pure
    $ RequestResponse
    $ JSON.toJSON
    $ case name of
      "Core.Token" -> RandomResponse.RandomValue $ JSON.toJSON $ (generate' arbitrary :: Token)
      "Core.Party" -> RandomResponse.RandomValue $ JSON.toJSON $ (generate' arbitrary :: Party)
      "Core.Contract" -> RandomResponse.RandomValue $ JSON.toJSON $ (generate' arbitrary :: Contract)
      _ -> RandomResponse.UnknownType t
  where
  generate' (MkGen g) = g (mkQCGen seed) size

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

instance Ord ValueId where
  compare (ValueId a) (ValueId b) = compare a b

instance Arbitrary Context where
  arbitrary =
    do
      parties <- arbitrary
      tokens <- arbitrary
      amounts <- listOf arbitraryPositiveInteger
      choiceNames <- listOf arbitraryChoiceName
      chosenNums <- listOf arbitraryInteger
      valueIds <- arbitrary
      values <- listOf arbitraryInteger
      times <- listOf arbitraryPositiveInteger
      choiceIds <- listOf $ ChoiceId <$> perturb arbitraryChoiceName choiceNames <*> perturb arbitrary parties
      caccounts <- fromList . nubBy ((==) `on` fst) <$> listOf ((,) <$> ((,) <$> perturb arbitrary parties <*> perturb arbitrary tokens) <*> perturb arbitraryPositiveInteger amounts)
      cchoices <- fromList . nubBy ((==) `on` fst) <$> listOf ((,) <$> perturb arbitrary choiceIds <*> perturb arbitraryInteger chosenNums)
      cboundValues <- fromList . nubBy ((==) `on` fst) <$> listOf ((,) <$> perturb arbitrary valueIds <*> perturb arbitraryInteger values)
      pure Context{..}
  shrink context@Context{..} =
    [context {parties = parties'} | parties' <- shrink parties]
      ++ [context {tokens = tokens'} | tokens' <- shrink tokens]
      ++ [context {amounts = amounts'} | amounts' <- shrink amounts]
      ++ [context {choiceNames = choiceNames'} | choiceNames' <- shrinkList shrinkChoiceName choiceNames]
      ++ [context {chosenNums = chosenNums'} | chosenNums' <- shrink chosenNums]
      ++ [context {valueIds = valueIds'} | valueIds' <- shrink valueIds]
      ++ [context {values = values'} | values' <- shrink values]
      ++ [context {times = times'} | times' <- shrink times]
      ++ [context {choiceIds = choiceIds'} | choiceIds' <- shrink choiceIds]
      ++ [context {caccounts = caccounts'} | caccounts' <- shrink caccounts]
      ++ [context {cchoices = cchoices'} | cchoices' <- shrink cchoices]
      ++ [context {cboundValues = cboundValues'} | cboundValues' <- shrink cboundValues]

instance Arbitrary Arith.Int where
  arbitrary = arbitraryInteger

instance SemiArbitrary Arith.Int where
  fromContext = times

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

instance SemiArbitrary Token where
  fromContext = tokens

instance Arbitrary Party where
  arbitrary =
    do
       isPubKeyHash <- frequency [(2, pure True), (8, pure False)]
       if isPubKeyHash
         then Address <$> arbitrary
         else Role <$> arbitraryFibonacci randomRoleNames
  shrink (Address _) = Role <$> randomRoleNames
  shrink (Role _)      = Role <$> randomRoleNames

instance SemiArbitrary Party where
  fromContext = parties

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

instance Arbitrary Contract where
  arbitrary = frequency [(95, semiArbitrary =<< arbitrary), (5, fst <$> goldenContract)]
  shrink (Pay a p t x c) = [Pay a' p t x c | a' <- shrink a] ++ [Pay a p' t x c | p' <- shrink p] ++ [Pay a p t' x c | t' <- shrink t] ++ [Pay a p t x' c | x' <- shrink x] ++ [Pay a p t x c' | c' <- shrink c]
  shrink (If o x y) = [If o' x y | o' <- shrink o] ++ [If o x' y | x' <- shrink x] ++ [If o x y' | y' <- shrink y]
  shrink (When a t c) = [When a' t c | a' <- shrink a] ++ [When a t' c | t' <- shrink t] ++ [When a t c' | c' <- shrink c]
  shrink (Let v x c) = [Let v' x c | v' <- shrink v] ++ [Let v x' c | x' <- shrink x] ++ [Let v x c' | c' <- shrink c]
  shrink (Assert o c) = [Assert o' c | o' <- shrink o] ++ [Assert o c' | c' <- shrink c]
  shrink _ = []

-- | Generate one of the golden contracts and its initial state.
goldenContract :: Gen (Contract, State_ext ())
goldenContract = (,) <$> elements goldenContracts <*> pure (State_ext [] [] [] 0 ())

goldenContracts :: [Contract]
goldenContracts = [ Swap.swapExample, Escrow.escrowExample ]

instance SemiArbitrary Contract where
  semiArbitrary context = sized \size -> arbitraryContractSized (min size 100 `div` 20) context -- Keep tests from growing too large to execute by capping the maximum contract depth at 5

-- | Generate a random case, weighted towards different contract constructs.
arbitraryCaseWeighted :: [(Int, Int, Int, Int, Int, Int)]  -- ^ The weights for contract terms.
                      -> Context                           -- ^ The Marlowe context.
                      -> Gen Case                          -- ^ Generator for a case.
arbitraryCaseWeighted w context =
  Case <$> semiArbitrary context <*> arbitraryContractWeighted w context

-- | Generate an arbitrary contract, weighted towards different contract constructs.
arbitraryContractWeighted :: [(Int, Int, Int, Int, Int, Int)]  -- ^ The weights of contract terms, which must eventually include `Close` as a posibility.
                          -> Context                           -- ^ The Marlowe context.
                          -> Gen Contract                      -- ^ Generator for a contract.
arbitraryContractWeighted ((wClose, wPay, wIf, wWhen, wLet, wAssert) : w) context =
  frequency
    [
      (wClose , pure Close)
    , (wPay   , Pay <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context <*> arbitraryContractWeighted w context)
    , (wIf    , If <$> semiArbitrary context <*> arbitraryContractWeighted w context <*> arbitraryContractWeighted w context)
    , (wWhen  , When <$> listOf (arbitraryCaseWeighted w context) `suchThat` ((<= length w) . length) <*> semiArbitrary context <*> arbitraryContractWeighted w context)
    , (wLet   , Let <$> semiArbitrary context <*> semiArbitrary context <*> arbitraryContractWeighted w context)
    , (wAssert, Assert <$> semiArbitrary context <*> arbitraryContractWeighted w context)
    ]
arbitraryContractWeighted [] _ = pure Close

-- | Default weights for contract terms.
defaultContractWeights :: (Int, Int, Int, Int, Int, Int)
defaultContractWeights = (35, 20, 10, 15, 20, 5)

-- | Generate a semi-random contract of a given depth.
arbitraryContractSized :: Int           -- ^ The maximum depth.
                       -> Context       -- ^ The Marlowe context.
                       -> Gen Contract  -- ^ Generator for a contract.
arbitraryContractSized = arbitraryContractWeighted . (`replicate` defaultContractWeights)

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

instance SemiArbitrary Value where
  semiArbitrary context =
    frequency
      [
        ( 8, uncurry AvailableMoney <$> perturb arbitrary (keys $ caccounts context))
      , (14, Constant <$> semiArbitrary context)
      , ( 8, NegValue <$> semiArbitrary context)
      , ( 8, AddValue <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, SubValue <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, MulValue <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, DivValue <$> semiArbitrary context <*> semiArbitrary context)
      , (10, ChoiceValue <$> semiArbitrary context)
      , ( 6, pure TimeIntervalStart)
      , ( 6, pure TimeIntervalEnd)
      , ( 8, UseValue <$> semiArbitrary context)
      , ( 8, Cond <$> semiArbitrary context <*> semiArbitrary context <*> semiArbitrary context)
      ]

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

instance SemiArbitrary Observation where
  semiArbitrary context =
    frequency
      [
        ( 8, AndObs <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, OrObs <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, NotObs <$> semiArbitrary context)
      , (16, ChoseSomething <$> semiArbitrary context)
      , ( 8, ValueGE <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, ValueGT <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, ValueLT <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, ValueLE <$> semiArbitrary context <*> semiArbitrary context)
      , ( 8, ValueEQ <$> semiArbitrary context <*> semiArbitrary context)
      , (10, pure TrueObs)
      , (10, pure FalseObs)
      ]

instance Arbitrary ChoiceId where
  arbitrary = ChoiceId <$> arbitraryChoiceName <*> arbitrary
  shrink (ChoiceId n p) = [ChoiceId n' p' | n' <- shrinkChoiceName n, p' <- shrink p]

instance SemiArbitrary ChoiceId where
  fromContext = choiceIds

instance Arbitrary Case where
  arbitrary = semiArbitrary =<< arbitrary
  shrink (Case a c)           = [Case a' c | a' <- shrink a] ++ [Case a c' | c' <- shrink c]

instance SemiArbitrary Case where
  semiArbitrary context = Case <$> semiArbitrary context <*> semiArbitrary context

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

instance Arbitrary ValueId where
  arbitrary = arbitraryFibonacci randomValueIds
  shrink = shrinkString (\(ValueId x) -> x) randomValueIds

instance SemiArbitrary ValueId where
  fromContext = valueIds

instance Arbitrary Payee where
  arbitrary =
    do
      isParty <- arbitrary
      if isParty
        then Party <$> arbitrary
        else Account <$> arbitrary
  shrink (Party x)   = Party <$> shrink x
  shrink (Account x) = Account <$> shrink x

instance SemiArbitrary Payee where
  semiArbitrary context =
      do
        party <- semiArbitrary context
        isParty <- arbitrary
        pure
          $ if isParty
              then Party party
              else Account party

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

instance SemiArbitrary Action where
  semiArbitrary context@Context{..} =
    let
      arbitraryDeposit =
        do
          (account, token) <- perturb arbitrary $ keys caccounts
          party <- semiArbitrary context
          Deposit account party token <$> semiArbitrary context
      arbitraryChoice = Choice <$> semiArbitrary context <*> semiArbitrary context
    in
      frequency
        [
          (3, arbitraryDeposit)
        , (6, arbitraryChoice)
        , (1, Notify <$> semiArbitrary context)
        ]

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

localJsonRoundtripSerialization :: TypeId -> JSON.Value -> SerializationResponse JSON.Value
localJsonRoundtripSerialization t@(TypeId name proxy) v = case fromTypeName name of
      Nothing -> UnknownType t
      (Just _) -> roundtrip proxy
    where
    roundtrip :: forall a. ToJSON a => FromJSON a => Proxy a -> SerializationResponse JSON.Value
    roundtrip _  = case JSON.fromJSON v :: Result a of
            Error str -> SerializationError str
            Success c ->  SerializationSuccess $ JSON.toJSON c
