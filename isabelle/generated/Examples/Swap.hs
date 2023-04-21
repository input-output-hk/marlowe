{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Examples.Swap(SwapParty_ext(..), swap, swapExample,
                 partialExecutionPathPayments, successfulExecutionPathPayments,
                 partialExecutionPathTransactions,
                 successfulExecutionPathTransactions)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Semantics;
import qualified Stringa;
import qualified SemanticsTypes;
import qualified Arith;

data SwapParty_ext a =
  SwapParty_ext SemanticsTypes.Party SemanticsTypes.Value SemanticsTypes.Token
    Arith.Int a
  deriving (Prelude.Read, Prelude.Show);

currency :: forall a. SwapParty_ext a -> SemanticsTypes.Token;
currency (SwapParty_ext party amount currency depositDeadline more) = currency;

amount :: forall a. SwapParty_ext a -> SemanticsTypes.Value;
amount (SwapParty_ext party amount currency depositDeadline more) = amount;

party :: forall a. SwapParty_ext a -> SemanticsTypes.Party;
party (SwapParty_ext party amount currency depositDeadline more) = party;

makePayment ::
  SwapParty_ext () ->
    SwapParty_ext () -> SemanticsTypes.Contract -> SemanticsTypes.Contract;
makePayment src dest =
  SemanticsTypes.Pay (party src) (SemanticsTypes.Party (party dest))
    (currency src) (amount src);

depositDeadline :: forall a. SwapParty_ext a -> Arith.Int;
depositDeadline (SwapParty_ext party amount currency depositDeadline more) =
  depositDeadline;

makeDeposit ::
  SwapParty_ext () -> SemanticsTypes.Contract -> SemanticsTypes.Contract;
makeDeposit sp continue =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Deposit (party sp) (party sp) (currency sp) (amount sp))
       continue]
    (depositDeadline sp) SemanticsTypes.Close;

swap :: SwapParty_ext () -> SwapParty_ext () -> SemanticsTypes.Contract;
swap p1 p2 =
  makeDeposit p1
    (makeDeposit p2
      (makePayment p1 p2 (makePayment p2 p1 SemanticsTypes.Close)));

adaToken :: SemanticsTypes.Token;
adaToken = SemanticsTypes.Token (Stringa.implode []) (Stringa.implode []);

adaProvider :: SemanticsTypes.Party;
adaProvider =
  SemanticsTypes.Role
    (Stringa.implode
      [Stringa.Char True False False False False False True False,
        Stringa.Char False False True False False True True False,
        Stringa.Char True False False False False True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char False False False False True False True False,
        Stringa.Char False True False False True True True False,
        Stringa.Char True True True True False True True False,
        Stringa.Char False True True False True True True False,
        Stringa.Char True False False True False True True False,
        Stringa.Char False False True False False True True False,
        Stringa.Char True False True False False True True False,
        Stringa.Char False True False False True True True False]);

dollarToken :: SemanticsTypes.Token;
dollarToken =
  SemanticsTypes.Token
    (Stringa.implode
      [Stringa.Char False False False True True True False False,
        Stringa.Char True False True False True True False False,
        Stringa.Char False True False False False True True False,
        Stringa.Char False True False False False True True False,
        Stringa.Char False True True False True True False False,
        Stringa.Char True False True False True True False False])
    (Stringa.implode
      [Stringa.Char False False True False False True True False,
        Stringa.Char True True True True False True True False,
        Stringa.Char False False True True False True True False,
        Stringa.Char False False True True False True True False,
        Stringa.Char True False False False False True True False,
        Stringa.Char False True False False True True True False]);

dollarProvider :: SemanticsTypes.Party;
dollarProvider =
  SemanticsTypes.Role
    (Stringa.implode
      [Stringa.Char False False True False False False True False,
        Stringa.Char True True True True False True True False,
        Stringa.Char False False True True False True True False,
        Stringa.Char False False True True False True True False,
        Stringa.Char True False False False False True True False,
        Stringa.Char False True False False True True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char False False False False True False True False,
        Stringa.Char False True False False True True True False,
        Stringa.Char True True True True False True True False,
        Stringa.Char False True True False True True True False,
        Stringa.Char True False False True False True True False,
        Stringa.Char False False True False False True True False,
        Stringa.Char True False True False False True True False,
        Stringa.Char False True False False True True True False]);

swapExample :: SemanticsTypes.Contract;
swapExample =
  swap (SwapParty_ext adaProvider
         (SemanticsTypes.Constant (Arith.Int_of_integer (10 :: Integer)))
         adaToken (Arith.Int_of_integer (1664812800000 :: Integer)) ())
    (SwapParty_ext dollarProvider
      (SemanticsTypes.Constant (Arith.Int_of_integer (20 :: Integer)))
      dollarToken (Arith.Int_of_integer (1664816400000 :: Integer)) ());

partialExecutionPathPayments :: [Semantics.Payment];
partialExecutionPathPayments =
  [Semantics.Payment adaProvider (SemanticsTypes.Party adaProvider) adaToken
     (Arith.Int_of_integer (10 :: Integer))];

successfulExecutionPathPayments :: [Semantics.Payment];
successfulExecutionPathPayments =
  [Semantics.Payment adaProvider (SemanticsTypes.Party dollarProvider) adaToken
     (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment dollarProvider (SemanticsTypes.Party adaProvider)
      dollarToken (Arith.Int_of_integer (20 :: Integer))];

partialExecutionPathTransactions :: [Semantics.Transaction_ext ()];
partialExecutionPathTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit adaProvider adaProvider adaToken
        (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664816400000 :: Integer),
        Arith.Int_of_integer (1664816600000 :: Integer))
      [] ()];

successfulExecutionPathTransactions :: [Semantics.Transaction_ext ()];
successfulExecutionPathTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit adaProvider adaProvider adaToken
        (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IDeposit dollarProvider dollarProvider dollarToken
         (Arith.Int_of_integer (20 :: Integer))]
      ()];

}
