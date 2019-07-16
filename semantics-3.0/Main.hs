module Main where

import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import qualified Data.Maybe                    as Maybe
import           Control.Monad.State
import           Test.Tasty
import           Test.Tasty.QuickCheck
import           Test.Tasty.HUnit
import           Debug.Trace

import           Semantics4
import           ZCBG2

main :: IO ()
main = print $ contractLifespan $ zeroCouponBondGuaranteed 1 2 3 1000 200 10 20
