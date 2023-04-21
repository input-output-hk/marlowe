{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.Core.Guarantees
  ( tests
  )
  where

import Arith (integer_of_nat)
import qualified Arith
import Control.Monad.IO.Class (MonadIO (..))
import qualified Data.Aeson as JSON
import Marlowe.Spec.Core.Arbitrary
  ( arbitraryPositiveInteger,
    arbitraryTimeIntervalAfter,
    arbitraryTransaction,
    arbitraryValidTransactions,
  )
import Marlowe.Spec.Core.Generators (genContext)
import Marlowe.Spec.Core.SemiArbitrary
  ( Context (..),
    SemiArbitrary (..),
    arbitraryContractWeighted,
  )
import Marlowe.Spec.Interpret
  ( InterpretJsonRequest,
    Request (..),
    Response (..),
  )
import Marlowe.Spec.Reproducible
  ( ReproducibleTest,
    generate,
    generateT,
    reproducibleProperty,
  )
import Marlowe.Utils (showAsJson)
import Orderings (Ord (..))
import PositiveAccounts (validAndPositive_state)
import QuickCheck.GenT
  ( Gen,
    MonadGen (..),
    frequency,
    suchThat,
  )
import Semantics
  ( TransactionOutput (..),
    TransactionOutputRecord_ext (..),
    Transaction_ext (..),
    emptyState,
    inputs,
    isQuiescent,
    maxTimeContract,
    txOutContract,
    txOutPayments,
    txOutState,
    txOutWarnings,
  )
import SemanticsTypes
  ( Contract (..),
    State_ext (..),
  )
import SingleInputTransactions (traceListToSingleInput)
import Test.QuickCheck (cover)
import Test.QuickCheck.Monadic (PropertyM, assert, monitor, run, stop)
import Test.QuickCheck.Property (counterexample)
import Test.Tasty (TestTree, testGroup)
import Timeout (isClosedAndEmpty)
import TransactionBound (maxTransactionsInitialState)

-- Property based tests correponding to theorems defined in Isabelle.
tests :: InterpretJsonRequest -> TestTree
tests i = testGroup "Guarantees"
    [
    -- TransactionBound.thy
    playTrace_only_accepts_maxTransactionsInitialStateTest i
    -- SingleInputTransactions.thy
    , traceToSingleInputIsEquivalentTest i
    -- QuiescentResults.thy
    , computeTransactionIsQuiescentTest i
    , playTraceIsQuiescentTest i
    -- Timeout.thy
    , timedOutTransaction_closes_contractTest i
    -- CloseIsSafe.thy
    , closeIsSafeTest i
    ]

-- TransactionBound.thy
--
-- lemma playTrace_only_accepts_maxTransactionsInitialState :
--    "playTrace sl c l = TransactionOutput txOut ⟹
--      length l ≤ maxTransactionsInitialState c"
playTrace_only_accepts_maxTransactionsInitialStateTest :: InterpretJsonRequest -> TestTree
playTrace_only_accepts_maxTransactionsInitialStateTest interpret = reproducibleProperty "lemma playTrace_only_accepts_maxTransactionsInitialState" do
    context <- run $ generateT $ genContext interpret
    (contract, Arith.Int_of_integer startTime, transactions) <- run $ generate $
        frequency
          [ (5, genContractStartTimeAndValidTransactions context)
          , (20, genContractStartTimeAndValidTransactions context `suchThat` \(_,_,l) -> not (null l))
          , (75, genContractStartTimeAndValidTransactions context `suchThat` \(_,_,l) -> length l > 1)
          ]
    let
        req :: Request JSON.Value
        req = PlayTrace startTime contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput TransactionOutputRecord_ext {}) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected maxTransactionsInitialState (" ++ show (maxTransactionsInitialState contract) ++ ")\n"
                ++ "to be an upper bound for the number of transactions (" ++ show (length transactions) ++ ")")
        stop $ cover 50.0 (length transactions > 1) "more than one transaction" $ toInteger (length transactions) <= integer_of_nat (maxTransactionsInitialState contract)
        :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err ) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"

genContractStartTimeAndValidTransactions :: Context -> Gen (Contract, Arith.Int, [Transaction_ext ()])
genContractStartTimeAndValidTransactions context = do
    c <- semiArbitrary context `suchThat` (/=Close)
    s <- arbitraryPositiveInteger
    t <- arbitraryValidTransactions (emptyState s) c
    pure (c, s, t)

isWhen :: Contract -> Bool
isWhen When {} = True
isWhen _ = False

isClose :: Contract -> Bool
isClose Close = True
isClose _ = False

-- SingleInputTransactions.thy
--
-- theorem traceToSingleInputIsEquivalent:
--    "playTrace sn co tral = playTrace sn co (traceListToSingleInput tral)"
traceToSingleInputIsEquivalentTest :: InterpretJsonRequest -> TestTree
traceToSingleInputIsEquivalentTest interpret = reproducibleProperty "theorem traceToSingleInputIsEquivalent" do
    context <- run $ generateT $ genContext interpret
    (contract, Arith.Int_of_integer startTime, transactions) <- run $ do
      generate $ (do
        c <- genArbitraryContracts context
        s <- arbitraryPositiveInteger
        t <- arbitraryValidTransactions (emptyState s) c
        pure (c,s,t)) `suchThat` \(_,_,t) -> t /= traceListToSingleInput t
    let
        numberOfInputs = foldr (\tx n -> n + length (inputs tx)) 0 transactions
        multipleInputs = PlayTrace startTime contract transactions
        singletonInput = PlayTrace startTime contract (traceListToSingleInput transactions)

    RequestResponse resMultipleInputs <- run $ liftIO $ interpret multipleInputs
    RequestResponse resSingletonInput <- run $ liftIO $ interpret singletonInput

    case (JSON.fromJSON resMultipleInputs, JSON.fromJSON resSingletonInput) of
      (JSON.Success (TransactionOutput o), JSON.Success (TransactionOutput _)) -> do
        monitor
          ( counterexample $
              "Result singleton Input: " ++ showAsJson resSingletonInput ++ "\n"
                ++ "Result multiple Inputs: " ++ showAsJson resMultipleInputs ++ "\n"
                ++ "Expected to be equal")
        stop $ cover 100.0 (integer_of_nat (maxTransactionsInitialState contract) > 2) "Contract can accept more than 2 transactions"
             $ cover 100.0 (numberOfInputs >= 2) "Transactions have 2 or more inputs"
             $ cover 40.0 (numberOfInputs >= 3) "Transactions have 3 or more inputs"
             $ cover 20.0 (not $ isClose $ txOutContract o) "Doesn't end up in close"
             $ resMultipleInputs == resSingletonInput
             :: PropertyM ReproducibleTest Bool
      (JSON.Success _, JSON.Success _) -> fail "TransactionError"
      _ -> fail "JSON parsing failed"
  where
  genArbitraryContracts :: Context -> Gen Contract
  genArbitraryContracts ctx = do
    arbitraryContractWeighted
      [ (0, 5, 10, 70, 10, 5)    -- A good contract for this test should never start with Close
      , (5, 10, 10, 60, 10, 5)
      , (15, 15, 10, 35, 20, 5)
      , (25, 20, 10, 30, 20, 5)
      , (25, 20, 10, 30, 20, 5)
      ]
      ctx
      `suchThat` (\c -> integer_of_nat (maxTransactionsInitialState c) > 2)

-- QuiescentResults.thy
--
-- theorem computeTransactionIsQuiescent:
--    "validAndPositive_state sta ⟹
--      computeTransaction traIn sta cont = TransactionOutput traOut ⟹
--        isQuiescent (txOutContract traOut) (txOutState traOut)"
-- TODO: Improve test-data quality. Less than 10% of txinput are empty transaction, and manually checking I noticed a lot of timeouted contracts
computeTransactionIsQuiescentTest :: InterpretJsonRequest -> TestTree
computeTransactionIsQuiescentTest interpret = reproducibleProperty "theorem computeTransactionIsQuiescent" do
    context <- run $ generateT $ genContext interpret
    (contract, state, transactions) <- run $ generate $
        frequency
          [ (45, genContractStateAndValidTransactions context `suchThat` \(_,_,l) -> not (null l))
          , (55, genContractStateAndValidTransactions context `suchThat` \(_,_,l) -> length l > 1)
          ]
    let
        transaction = head transactions
        req :: Request JSON.Value
        req = ComputeTransaction transaction state contract

    RequestResponse res <- run $ liftIO $ interpret req
    case JSON.fromJSON res of
      JSON.Success (TransactionOutput o) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Response: " ++ showAsJson res ++ "\n"
                ++ "Expected reponse to be quiescent")
        stop $ cover 30.0 (not (null (inputs transaction))) "Non empty transaction"
             $ cover 10.0 (isWhen $ txOutContract o) "Output contract is a When statement"
             $ isQuiescent (txOutContract o) (txOutState o)
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"

genContractStateAndValidTransactions :: Context -> Gen (Contract, State_ext (), [Transaction_ext ()])
genContractStateAndValidTransactions context = do
    c <- semiArbitrary context `suchThat` (/=Close)
    s <- semiArbitrary context
    t <- arbitraryValidTransactions s c
    pure (c, s, t)

-- QuiescentResults.thy
--
-- theorem playTraceIsQuiescent:
--    "playTrace sl cont (Cons h t) = TransactionOutput traOut ⟹
--      isQuiescent (txOutContract traOut) (txOutState traOut)"
playTraceIsQuiescentTest :: InterpretJsonRequest -> TestTree
playTraceIsQuiescentTest interpret = reproducibleProperty "theorem playTraceIsQuiescent" do
    context <- run $ generateT $ genContext interpret
    (contract, Arith.Int_of_integer startTime, transactions) <- run $ generate $
        frequency
          [ (45, genContractStartTimeAndValidTransactions context `suchThat` \(_,_,l) -> not (null l))
          , (55, genContractStartTimeAndValidTransactions context `suchThat` \(_,_,l) -> length l > 1)
          ]
    let
        req :: Request JSON.Value
        req = PlayTrace startTime contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput o) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Response: " ++ showAsJson res ++ "\n"
                ++ "Expected reponse to be quiescent" )
        assert $ isQuiescent (txOutContract o) (txOutState o)
      JSON.Success (TransactionError err) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"

-- Timeout.thy
--
-- theorem timedOutTransaction_closes_contract:
--    "validAndPositive_state sta
--       ⟹  iniTime ≥ minTime sta
--       ⟹  iniTime ≥ maxTimeContract cont
--       ⟹  endTime ≥ iniTime
--       ⟹  accounts sta ≠ [] ∨ cont ≠ Close
--       ⟹  isClosedAndEmpty (computeTransaction ⦇ interval = (iniTime, endTime), inputs = [] ⦈ sta cont)"
timedOutTransaction_closes_contractTest :: InterpretJsonRequest -> TestTree
timedOutTransaction_closes_contractTest interpret = reproducibleProperty "theorem timedOutTransaction_closes_contract" do
    context <- run $ generateT $ genContext interpret
    (contract, state@(State_ext _ _ _ minTime' _)) <- run $ generate $ (do
      c <- semiArbitrary context
      s <- semiArbitrary context `suchThat` validAndPositive_state
      pure (c,s)) `suchThat` \(contract, State_ext accounts _ _ _ _) -> not (null accounts) || contract /= Close
    interval <- run $ generate $ arbitraryTimeIntervalAfter minTime' `suchThat` \(iniTime, endTime) ->
           (iniTime `greater_eq` minTime')
        && (iniTime `greater_eq` maxTimeContract contract)
        && (endTime `greater_eq` iniTime)

    let transaction = Transaction_ext interval [] ()
        req :: Request JSON.Value
        req = ComputeTransaction transaction state contract

    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success txOut@(TransactionOutput o) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "txOutContract: " ++ show (txOutContract o)
                ++ "txOutState: " ++ show (txOutState o))
        stop $ cover 100.0 (null (inputs transaction)) "Transaction without inputs"
             $ cover 10.0 (length (txOutPayments o) > 1) "Timeout contract produces payments"
             $ cover 70.0 (integer_of_nat (maxTransactionsInitialState contract) >= 1) "At least 1 transaction"
             $ cover 10.0 (integer_of_nat (maxTransactionsInitialState contract) >= 3) "At least 3 transactions"
             $ isClosedAndEmpty txOut
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"
  where
    greater_eq = flip less_eq

-- CloseIsSafe.thy
--
-- theorem closeIsSafe :
--    "computeTransaction tra sta Close = TransactionOutput trec ⟹  txOutWarnings trec = []"
closeIsSafeTest :: InterpretJsonRequest -> TestTree
closeIsSafeTest interpret = reproducibleProperty "theorem closeIsSafe" do
    -- NOTE: To satisfy the premise that computeTransaction on a Close results in a succesful TransactionOutput
    --       we need for the state to have at least one account (Which we guarantee by using the state with size generator)
    --       This is also shown by the cover test below, which show that all valid transactions necesarly are the empty transaction
    --       and that it always produce payments. If the accounts were empty then an empty transaction would yield
    --       the error Useless Transaction, and moreover, there isn't a valid transaction possible
    --       TODO: Make lemmas about these last two observations.
    context <- run $ generateT $ genContext interpret
    state@(State_ext _ _ _ startTime _) <- run $ generate $ semiArbitrary context

    transaction <-  run $ generate $ arbitraryTransaction state Close `suchThat` \(Transaction_ext (_,upper) _ _) -> startTime `less_eq` upper
    let req :: Request JSON.Value
        req = ComputeTransaction transaction state Close

    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput trec) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Expected: no warnings\n"
                ++ "Actual: " ++ show (txOutWarnings trec))
        stop $ cover 100.0 (null (inputs transaction)) "Transaction without inputs"
             $ cover 100.0 (not (null (txOutPayments trec))) "Close contract produces payments"
             $ null (txOutWarnings trec)
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err ) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"
