module Main where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import Control.Monad.State
import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Semantics as S
import SPJModel hiding (Contract(..))
import qualified SPJModel as SPJ
import CrowdFunding
import DepositIncentive
import Escrow

evaluateMaximumValueTests :: [TestTree]
evaluateMaximumValueTests = [evalCrowdFunding, evalDepositIncentive, evalEscrow]
  where
    evalCrowdFunding = testCase "Evaluate CrowdFunding balances" $ do
        let bounds = Map.fromList [(Right $ IdentChoice 1, 1000), (Right $ IdentChoice 2, 1000),
                (Right $ IdentChoice 3, 1000), (Right $ IdentChoice 4, 1000)]
        let balances = evaluateMaximumValue bounds crowdFunding
        balances @?= Map.fromList [ (1, Balance 0 1000),
                                    (2, Balance 0 1000),
                                    (3, Balance 0 1000),
                                    (4, Balance 0 1000),
                                    (5, Balance 4000 0) ]

    evalDepositIncentive = testCase "Evaluate DepositIncentive balances" $ do
        let balances = evaluateMaximumValue Map.empty depositIncentive
        balances @?= Map.fromList [ (1, Balance 20 0),
                                    (2, Balance 0 20) ]

    evalEscrow = testCase "Evaluate Escrow balances" $ do
        let balances = evaluateMaximumValue Map.empty escrow
        balances @?= Map.fromList [ (1, Balance 0 450),
                                    (2, Balance 450 0) ]

tests :: [TestTree]
tests = evaluateMaximumValueTests

main :: IO ()
main = do
    print $ zcbMarlowe 100 12345 1 2
    let c = SPJ.One
    print $ translateSPJContractToMarlowe 1 8 (SPJ.One)
    print $ translateSPJContractToMarlowe 1 8 (SPJ.Give $ SPJ.One)
    defaultMain (testGroup "Marlowe Tests" tests)
