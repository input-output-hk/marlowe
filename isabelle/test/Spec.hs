-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | Marlowe specification tests.
--
-----------------------------------------------------------------------------


{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}


module Main
  ( -- * Testing
    main
  ) where


import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@=?))
import qualified Spec.Core.Examples.Swap (tests)
import qualified Spec.Core.Serialization.Json (tests)

-- | Entry point for the tests.
main :: IO ()
main = defaultMain tests


-- | Run the tests.
tests :: TestTree
tests =
  testGroup "Marlowe Spec"
    [ testGroup "Examples"
      [ Spec.Core.Examples.Swap.tests
      ]
    , Spec.Core.Serialization.Json.tests
    ]
