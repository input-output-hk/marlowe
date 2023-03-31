module Main where

import Test.Tasty (defaultMain)
import Marlowe.Spec (tests)
import Marlowe.Spec.LocalInterpret (interpretLocal)

main :: IO ()
main = defaultMain $ tests interpretLocal
