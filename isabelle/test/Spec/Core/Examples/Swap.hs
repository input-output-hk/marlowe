{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Spec.Core.Examples.Swap (tests) where


import qualified Arith;
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@=?))
import SemanticsTypes (Contract (..), Party (..), Payee(..), Token, Value, Case(..), Action(..))

------- Contract definition -------
-- FIXME, this should be exported from Isabelle or manually placed in a common module.
type Timeout = Arith.Int

data SwapParty = SwapParty { party           :: Party
                           , currency        :: Token
                           , amount          :: Value
                           , depositDeadline :: Timeout
                           }

makeDeposit :: SwapParty -> Contract -> Contract
makeDeposit sp continuation =
  When [ Case (Deposit (party sp) (party sp) (currency sp) (amount sp))
              continuation
       ] (depositDeadline sp)
         Close

makePayment :: SwapParty -> SwapParty -> Contract -> Contract
makePayment src dest =
  Pay (party src) (Party $ party dest) (currency src) (amount src)

contract :: SwapParty -> SwapParty -> Contract
contract firstParty secondParty =
         makeDeposit firstParty
         $ makeDeposit secondParty
         $ makePayment firstParty secondParty
         $ makePayment secondParty firstParty
           Close

------- Contract tests -------
tests :: TestTree
tests = testGroup "Swap"
    [ testCase "Golden path" testGoldenPath
    ]

-- p :: Party
-- p = Role "test party"
-- adaProvider, dollarProvider :: SwapParty
-- adaProvider = SwapParty { party = Role "Ada provider"
--                         , currency = ada
--                         , amount = amountOfLovelace
--                         }
-- dollarProvider = SwapParty { party = Role "Dollar provider"
--                            , currency = dollars
--                            , amount = amountOfDollars
--                            }

testGoldenPath :: IO ()
testGoldenPath = do
  putStrLn "test golden path"
  return ()
