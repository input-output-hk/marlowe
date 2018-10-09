module Main where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import Control.Monad.State

import Semantics as S
import SPJModel hiding (Contract(..))
import qualified SPJModel as SPJ
import CrowdFunding
import DepositIncentive
import Escrow


main :: IO ()
main = do
    print $ zcbMarlowe 100 12345 1 2
    let c = SPJ.One
    print $ translateSPJContractToMarlowe 1 8 (SPJ.One)
    print $ translateSPJContractToMarlowe 1 8 (SPJ.Give $ SPJ.One)
    print $ evaluateMaximumValue Map.empty (
        CommitCash (IdentCC 1) 1 (Value 123) 10 20
            (Pay (IdentPay 1) 1 2 (Value 120) 5 Null)
            (Pay (IdentPay 1) 1 2 (Value 122) 5 Null))


    let bounds = Map.fromList [(Right $ IdentChoice 1, 1000), (Right $ IdentChoice 2, 1000),
            (Right $ IdentChoice 3, 1000), (Right $ IdentChoice 4, 1000)]
    print $ evaluateMaximumValue bounds crowdFunding
    print $ evaluateMaximumValue bounds depositIncentive
    print $ evaluateMaximumValue bounds escrow
