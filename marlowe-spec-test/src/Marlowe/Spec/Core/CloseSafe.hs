{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Marlowe.Spec.Core.CloseSafe where

import Test.Tasty (TestTree, testGroup)
import qualified SemanticsTypes as C
import qualified Semantics as C
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request (..), Response (..))
import Test.QuickCheck.Monadic (run, monitor, assert, pre)
import Marlowe.Spec.Core.Arbitrary (genState, genTransaction)
import Semantics (TransactionOutput (..), txOutWarnings)
import qualified Data.Aeson as JSON
import Marlowe.Spec.Reproducible (reproducibleProperty, generateT)
import Control.Monad.IO.Class (MonadIO(..))
import Test.QuickCheck.Property (counterexample)
import Marlowe.Utils (showAsJson)

tests :: InterpretJsonRequest -> TestTree
tests i =
  testGroup
    "CloseSafe"
    [closeIsSafeTest i]

-- theorem closeIsSafe :
--    "computeTransaction tra sta Close = TransactionOutput trec ⟹  txOutWarnings trec = []"
closeIsSafeTest :: InterpretJsonRequest -> TestTree
closeIsSafeTest interpret = reproducibleProperty "Close is safe" do
  state <- run $ generateT $ genState interpret
  txIn <- run $ generateT $ genTransaction interpret
  let req :: Request JSON.Value
      req = ComputeTransaction txIn state C.Close

  RequestResponse res <- run $ liftIO $ interpret req

  case JSON.fromJSON res of
    JSON.Success (TransactionOutput trec) -> do
      let expected :: [C.TransactionWarning]
          expected = mempty
      monitor
        ( counterexample $
            "Request: " ++ showAsJson req ++ "\n"
              ++ "Expected: " ++ show expected ++ "\n"
              ++ "Actual: " ++ show (txOutWarnings trec))
      assert (txOutWarnings trec == expected)
    JSON.Success _ -> pre False
    _ -> fail "JSON parsing failed!"
