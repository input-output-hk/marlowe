{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module Main where

import Test.Tasty (defaultMainWithIngredients, defaultIngredients, includingOptions)
import Marlowe.Spec.ClientProcess (CliPath(..), TraceCP, eval, withClientProcess)
import Test.Tasty.Options (OptionDescription (Option), lookupOption)
import Data.Proxy (Proxy(..))
import Test.Tasty.Runners (parseOptions)
import Marlowe.Spec (tests)
import System.Environment (setEnv)
main :: IO ()
main = do
  let
    tastyOptions =
      [ Option (Proxy :: Proxy CliPath)
      , Option (Proxy :: Proxy TraceCP)
      ]
    tastyIngredients = defaultIngredients <> [includingOptions tastyOptions]
    testsCP = withClientProcess (\getCP -> tests $ eval getCP)
  optSet <- parseOptions tastyIngredients testsCP
  case lookupOption optSet of
    UndefinedCliPath -> do
      putStrLn "The client process wasn't specified. You can use the '-c' option to set it"
      putStrLn "for more options execute with --help"
    _ -> do
      -- FIX: We currently need to limit the number of threads to 1 because the ClientProcess module
      -- is not thread safe for the moment.
      setEnv "TASTY_NUM_THREADS" "1"
      defaultMainWithIngredients tastyIngredients testsCP
