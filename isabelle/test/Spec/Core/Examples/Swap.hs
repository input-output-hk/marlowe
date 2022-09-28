{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Spec.Core.Examples.Swap (tests) where


import qualified Arith;
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import SemanticsTypes (Contract (..), Party (..), Payee(..), Token(..), Value(..), Case(..), Action(..), Input(..), equal_Contract)
import Semantics (TransactionOutput(..), Transaction_ext(..), TransactionWarning(..), Payment(..), playTrace, txOutContract, txOutWarnings, txOutPayments, equal_TransactionWarning, equal_Payment)


-- FIXME: Isabelle doesn't export type synonims by default, see if we can fix that or
--        make a common module that acts as a wrapper with the aliases and the orphan instances.
type Timeout = Arith.Int

-- FIXME: I wasn't able to export some Eq instances (it does export the equal_X functions). See if
--        we can resolve that or at least put the manual instances in a separate module.
instance Eq Contract where {
  a == b = equal_Contract a b;
};

-- FIXME: Make all the show instances.
instance Show Contract where
  show Close = "Close"
  show (Pay _ _ _ _ _) = "Pay"
  show (If _ _ _) = "If"
  show (When _ _ _) = "When"
  show (Let _ _ _) = "Let"
  show (Assert _ _) = "Assert"

instance Eq TransactionWarning where {
  a == b = equal_TransactionWarning a b;
}

instance Show TransactionWarning where
  show (TransactionNonPositiveDeposit _ _ _ _) = "TransactionNonPositiveDeposit"
  show (TransactionNonPositivePay _ _ _ _) = "TransactionNonPositivePay"
  show (TransactionPartialPay _ _ _ _ _) = "TransactionPartialPay"
  show (TransactionShadowing _ _ _) = "TransactionShadowing"
  show (TransactionAssertionFailed) = "TransactionAssertionFailed"


instance Eq Payment where {
  a == b = equal_Payment a b;
}

instance Show Payment where
  show (Payment _ _ _ _) = "Payment"

------- Contract definition -------

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


partyA, partyB :: Party
partyA = Role "Token A provider"
partyB = Role "Token B provider"

tokenA, tokenB :: Token
tokenA = Token "symbol-a" "a"
tokenB = Token "symbol-b" "b"

amountA, amountB :: Arith.Int
amountA = Arith.Int_of_integer 10
amountB = Arith.Int_of_integer 20

tokenAProvider, tokenBProvider :: SwapParty
tokenAProvider = SwapParty { party = partyA
                           , currency = tokenA
                           , amount = Constant amountA
                           , depositDeadline = Arith.Int_of_integer 10
                           }
tokenBProvider = SwapParty { party = partyB
                           , currency = tokenB
                           , amount = Constant amountB
                           , depositDeadline = Arith.Int_of_integer 20
                           }
testGoldenPath :: IO ()
testGoldenPath = do
  let inputs = [ IDeposit partyA partyA tokenA amountA
               , IDeposit partyB partyB tokenB amountB
               ]
  let singleTx = Transaction_ext (Arith.Int_of_integer 0, Arith.Int_of_integer 5) inputs ()
  case playTrace (Arith.Int_of_integer 1) (contract tokenAProvider tokenBProvider) [singleTx] of
    TransactionError _ -> assertFailure "playTrace failed its execution"
    TransactionOutput o -> do
      txOutContract o @?= Close
      txOutWarnings o @?= []
      txOutPayments o @?=
                          [ Payment partyA (Party $ partyB) tokenA amountA
                          , Payment partyB (Party $ partyA) tokenB amountB
                          ]


