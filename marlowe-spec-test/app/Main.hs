{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}


module Main where

import Test.Tasty (defaultMainWithIngredients, defaultIngredients, includingOptions)
import Marlowe.Spec.ClientProcess (CliPath(..), TraceCP, PoolSize, eval, withClientProcess)
import Test.Tasty.Options (OptionDescription (Option), lookupOption)
import Data.Proxy (Proxy(..))
import Test.Tasty.Runners (parseOptions)
import Marlowe.Spec (tests)

main :: IO ()
main = do
  let
    tastyOptions =
      [ Option (Proxy @CliPath)
      , Option (Proxy @TraceCP)
      , Option (Proxy @PoolSize)
      ]
    tastyIngredients = defaultIngredients <> [includingOptions tastyOptions]
    testsCP = withClientProcess (\getCP -> tests $ eval getCP)
  optSet <- parseOptions tastyIngredients testsCP
  case lookupOption optSet of
    UndefinedCliPath -> do
      putStrLn "The client process wasn't specified. You can use the '-c' option to set it"
      putStrLn "for more options execute with --help"
    _ -> defaultMainWithIngredients tastyIngredients testsCP
