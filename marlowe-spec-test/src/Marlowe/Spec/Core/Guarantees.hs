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
import Marlowe.Spec.Core.Arbitrary (arbitraryTimeIntervalAfter)
import Marlowe.Spec.Core.SemiArbitrary
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
    frequency,
    suchThat,
  )
import Semantics
  ( TransactionOutput (..),
    TransactionOutputRecord_ext (..),
    Transaction_ext (..),
    inputs,
    isQuiescent,
    maxTimeContract,
    txOutPayments,
    txOutWarnings,
  )
import SemanticsTypes
  ( Contract (..),
    State_ext (..),
  )
import SingleInputTransactions (traceListToSingleInput)
import Test.QuickCheck (cover)
import Test.QuickCheck.Monadic (PropertyM, assert, monitor, pre, run, stop)
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
    (contract, State_ext _ _ _ (Arith.Int_of_integer startTime) _, transactions) <- run $ generate $
        frequency
          [ (5, genContractStateAndValidTransactions context)
          , (20, genContractStateAndValidTransactions context `suchThat` \(_,_,l) -> not (null l))
          , (75, genContractStateAndValidTransactions context `suchThat` \(_,_,l) -> length l > 1)
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
      JSON.Success (TransactionError _ ) -> pre False
      _ -> fail "JSON parsing failed!"

genContractStateAndValidTransactions :: Context -> Gen (Contract, State_ext (), [Transaction_ext ()])
genContractStateAndValidTransactions context = do
    c <- semiArbitrary context `suchThat` (/=Close)
    s <- semiArbitrary context
    t <- arbitraryValidTransactions s c
    pure (c,s,t)

-- SingleInputTransactions.thy
--
-- theorem traceToSingleInputIsEquivalent:
--    "playTrace sn co tral = playTrace sn co (traceListToSingleInput tral)"
traceToSingleInputIsEquivalentTest :: InterpretJsonRequest -> TestTree
traceToSingleInputIsEquivalentTest interpret = reproducibleProperty "theorem traceToSingleInputIsEquivalent" do
    context <- run $ generateT $ genContext interpret
    (contract, State_ext _ _ _ (Arith.Int_of_integer startTime) _, transactions) <- run $ generate $ (do
        (_,c) <- semiArbitrary context `suchThat` (\(b,c) -> b && integer_of_nat (maxTransactionsInitialState c) > 2)
        s <- semiArbitrary context
        t <- arbitraryValidTransactions s c
        pure (c,s,t)) `suchThat` \(_,_,t') -> t' /= traceListToSingleInput t'

    let
        multipleInputs = PlayTrace startTime contract transactions
        singletonInput = PlayTrace startTime contract (traceListToSingleInput transactions)

    RequestResponse resMultipleInputs <- run $ liftIO $ interpret multipleInputs
    RequestResponse resSingletonInput <- run $ liftIO $ interpret singletonInput

    case (JSON.fromJSON resMultipleInputs, JSON.fromJSON resSingletonInput) of
      (JSON.Success (TransactionOutput _), JSON.Success (TransactionOutput _)) -> do
        monitor
          ( counterexample $
              "Result singleton Input: " ++ showAsJson resSingletonInput ++ "\n"
                ++ "Result multiple Inputs: " ++ showAsJson resMultipleInputs ++ "\n"
                ++ "Expected to be equal")
        assert $ resMultipleInputs == resSingletonInput
      (JSON.Success (TransactionError _), JSON.Success _) -> pre False
      (JSON.Success _ , JSON.Success (TransactionError _)) -> pre False
      _ -> fail "JSON parsing failed"

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
      JSON.Success (TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Response: " ++ showAsJson res ++ "\n"
                ++ "Expected reponse to be quiescent")
        stop $ cover 30.0 (not (null (inputs transaction))) "Non empty transaction"
             $ cover 10.0 (isWhen txOutContract) "Output contract is a When statement"
             $ isQuiescent txOutContract txOutState
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err ) -> fail $ "Unexpected Transaction Error: " ++ show err
      _ -> fail "JSON parsing failed!"
  where
    isWhen :: Contract -> Bool
    isWhen When {} = True
    isWhen _ = False

-- QuiescentResults.thy
--
-- theorem playTraceIsQuiescent:
--    "playTrace sl cont (Cons h t) = TransactionOutput traOut ⟹
--      isQuiescent (txOutContract traOut) (txOutState traOut)"
playTraceIsQuiescentTest :: InterpretJsonRequest -> TestTree
playTraceIsQuiescentTest interpret = reproducibleProperty "theorem playTraceIsQuiescent" do
    context <- run $ generateT $ genContext interpret
    (contract, State_ext _ _ _ (Arith.Int_of_integer startTime) _, transactions) <- run $ generate $
        frequency
          [ (45, genContractStateAndValidTransactions context `suchThat` \(_,_,l) -> not (null l))
          , (55, genContractStateAndValidTransactions context `suchThat` \(_,_,l) -> length l > 1)
          ]
    let
        req :: Request JSON.Value
        req = PlayTrace startTime contract transactions
    RequestResponse res <- run $ liftIO $ interpret req

    case JSON.fromJSON res of
      JSON.Success (TransactionOutput (TransactionOutputRecord_ext _ _ txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "Response: " ++ showAsJson res ++ "\n"
                ++ "Expected reponse to be quiescent" )
        assert $ isQuiescent txOutContract txOutState
      JSON.Success (TransactionError _ ) -> pre False
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
      JSON.Success txOut@(TransactionOutput (TransactionOutputRecord_ext _ txOutPayment txOutState txOutContract _)) -> do
        monitor
          ( counterexample $
              "Request: " ++ showAsJson req ++ "\n"
                ++ "txOutContract: " ++ show txOutContract
                ++ "txOutState: " ++ show txOutState)
        stop $ cover 100.0 (null (inputs transaction)) "Transaction without inputs"
             $ cover 10.0 (length txOutPayment > 1) "Timeout contract produces payments"
             $ cover 70.0 (integer_of_nat (maxTransactionsInitialState contract) >= 1) "At least 1 transaction"
             $ cover 10.0 (integer_of_nat (maxTransactionsInitialState contract) >= 3) "At least 3 transactions"
             $ isClosedAndEmpty txOut
             :: PropertyM ReproducibleTest Bool
      JSON.Success (TransactionError err ) -> fail $ "Unexpected Transaction Error: " ++ show err
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
