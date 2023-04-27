{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Examples.Escrow(EscrowArgs_ext(..), escrow, escrowExample,
                   confirmClaimPayments, dismissClaimPayments,
                   confirmProblemPayments, confirmClaimTransactions,
                   dismissClaimTransactions, confirmProblemTransactions,
                   everythingIsAlrightPayments, everythingIsAlrightTransactions)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Semantics;
import qualified Str;
import qualified SemanticsTypes;
import qualified Arith;

data EscrowArgs_ext a =
  EscrowArgs_ext SemanticsTypes.Value SemanticsTypes.Token SemanticsTypes.Party
    SemanticsTypes.Party SemanticsTypes.Party Arith.Int Arith.Int Arith.Int
    Arith.Int a
  deriving (Prelude.Read, Prelude.Show);

buyer :: SemanticsTypes.Party;
buyer =
  SemanticsTypes.Role
    (Str.implode
      [Str.Char False True False False False False True False,
        Str.Char True False True False True True True False,
        Str.Char True False False True True True True False,
        Str.Char True False True False False True True False,
        Str.Char False True False False True True True False]);

paymentDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
paymentDeadline
  (EscrowArgs_ext price token buyerParty sellerParty mediatorParty
    paymentDeadline complaintDeadline disputeDeadline mediationDeadline more)
  = paymentDeadline;

token :: forall a. EscrowArgs_ext a -> SemanticsTypes.Token;
token (EscrowArgs_ext price token buyerParty sellerParty mediatorParty
        paymentDeadline complaintDeadline disputeDeadline mediationDeadline
        more)
  = token;

price :: forall a. EscrowArgs_ext a -> SemanticsTypes.Value;
price (EscrowArgs_ext price token buyerParty sellerParty mediatorParty
        paymentDeadline complaintDeadline disputeDeadline mediationDeadline
        more)
  = price;

seller :: SemanticsTypes.Party;
seller =
  SemanticsTypes.Role
    (Str.implode
      [Str.Char True True False False True False True False,
        Str.Char True False True False False True True False,
        Str.Char False False True True False True True False,
        Str.Char False False True True False True True False,
        Str.Char True False True False False True True False,
        Str.Char False True False False True True True False]);

complaintDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
complaintDeadline
  (EscrowArgs_ext price token buyerParty sellerParty mediatorParty
    paymentDeadline complaintDeadline disputeDeadline mediationDeadline more)
  = complaintDeadline;

disputeDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
disputeDeadline
  (EscrowArgs_ext price token buyerParty sellerParty mediatorParty
    paymentDeadline complaintDeadline disputeDeadline mediationDeadline more)
  = disputeDeadline;

mediationDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
mediationDeadline
  (EscrowArgs_ext price token buyerParty sellerParty mediatorParty
    paymentDeadline complaintDeadline disputeDeadline mediationDeadline more)
  = mediationDeadline;

mediator :: SemanticsTypes.Party;
mediator =
  SemanticsTypes.Role
    (Str.implode
      [Str.Char True False True True False False True False,
        Str.Char True False True False False True True False,
        Str.Char False False True False False True True False,
        Str.Char True False False True False True True False,
        Str.Char True False False False False True True False,
        Str.Char False False True False True True True False,
        Str.Char True True True True False True True False,
        Str.Char False True False False True True True False]);

mediation :: EscrowArgs_ext () -> SemanticsTypes.Contract;
mediation args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Choice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char False False True False False False True False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char True False True True False True True False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char True True False False True True True False,
               Str.Char False False False False False True False False,
               Str.Char True True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False False False False True True False,
               Str.Char True False False True False True True False,
               Str.Char True False True True False True True False])
           mediator)
         [SemanticsTypes.Bound Arith.zero_int Arith.zero_int])
       (SemanticsTypes.Pay buyer (SemanticsTypes.Account seller) (token args)
         (price args) SemanticsTypes.Close),
      SemanticsTypes.Case
        (SemanticsTypes.Choice
          (SemanticsTypes.ChoiceId
            (Str.implode
              [Str.Char True True False False False False True False,
                Str.Char True True True True False True True False,
                Str.Char False True True True False True True False,
                Str.Char False True True False False True True False,
                Str.Char True False False True False True True False,
                Str.Char False True False False True True True False,
                Str.Char True False True True False True True False,
                Str.Char False False False False False True False False,
                Str.Char True True False False False True True False,
                Str.Char False False True True False True True False,
                Str.Char True False False False False True True False,
                Str.Char True False False True False True True False,
                Str.Char True False True True False True True False])
            mediator)
          [SemanticsTypes.Bound Arith.one_int Arith.one_int])
        SemanticsTypes.Close]
    (mediationDeadline args) SemanticsTypes.Close;

dispute :: EscrowArgs_ext () -> SemanticsTypes.Contract;
dispute args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Choice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char True True False False False False True False,
               Str.Char True True True True False True True False,
               Str.Char False True True True False True True False,
               Str.Char False True True False False True True False,
               Str.Char True False False True False True True False,
               Str.Char False True False False True True True False,
               Str.Char True False True True False True True False,
               Str.Char False False False False False True False False,
               Str.Char False False False False True True True False,
               Str.Char False True False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False True False False True True False,
               Str.Char True False True True False True True False])
           seller)
         [SemanticsTypes.Bound Arith.one_int Arith.one_int])
       SemanticsTypes.Close,
      SemanticsTypes.Case
        (SemanticsTypes.Choice
          (SemanticsTypes.ChoiceId
            (Str.implode
              [Str.Char False False True False False False True False,
                Str.Char True False False True False True True False,
                Str.Char True True False False True True True False,
                Str.Char False False False False True True True False,
                Str.Char True False True False True True True False,
                Str.Char False False True False True True True False,
                Str.Char True False True False False True True False,
                Str.Char False False False False False True False False,
                Str.Char False False False False True True True False,
                Str.Char False True False False True True True False,
                Str.Char True True True True False True True False,
                Str.Char False True False False False True True False,
                Str.Char False False True True False True True False,
                Str.Char True False True False False True True False,
                Str.Char True False True True False True True False])
            seller)
          [SemanticsTypes.Bound Arith.zero_int Arith.zero_int])
        (mediation args)]
    (disputeDeadline args) SemanticsTypes.Close;

report :: EscrowArgs_ext () -> SemanticsTypes.Contract;
report args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Choice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char True False True False False False True False,
               Str.Char False True True False True True True False,
               Str.Char True False True False False True True False,
               Str.Char False True False False True True True False,
               Str.Char True False False True True True True False,
               Str.Char False False True False True True True False,
               Str.Char False False False True False True True False,
               Str.Char True False False True False True True False,
               Str.Char False True True True False True True False,
               Str.Char True True True False False True True False,
               Str.Char False False False False False True False False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char False False False False False True False False,
               Str.Char True False False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char False True False False True True True False,
               Str.Char True False False True False True True False,
               Str.Char True True True False False True True False,
               Str.Char False False False True False True True False,
               Str.Char False False True False True True True False])
           buyer)
         [SemanticsTypes.Bound Arith.zero_int Arith.zero_int])
       SemanticsTypes.Close,
      SemanticsTypes.Case
        (SemanticsTypes.Choice
          (SemanticsTypes.ChoiceId
            (Str.implode
              [Str.Char False True False False True False True False,
                Str.Char True False True False False True True False,
                Str.Char False False False False True True True False,
                Str.Char True True True True False True True False,
                Str.Char False True False False True True True False,
                Str.Char False False True False True True True False,
                Str.Char False False False False False True False False,
                Str.Char False False False False True True True False,
                Str.Char False True False False True True True False,
                Str.Char True True True True False True True False,
                Str.Char False True False False False True True False,
                Str.Char False False True True False True True False,
                Str.Char True False True False False True True False,
                Str.Char True False True True False True True False])
            buyer)
          [SemanticsTypes.Bound Arith.one_int Arith.one_int])
        (SemanticsTypes.Pay seller (SemanticsTypes.Account buyer) (token args)
          (price args) (dispute args))]
    (complaintDeadline args) SemanticsTypes.Close;

escrow :: EscrowArgs_ext () -> SemanticsTypes.Contract;
escrow args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Deposit seller buyer (token args) (price args))
       (report args)]
    (paymentDeadline args) SemanticsTypes.Close;

exampleArgs :: EscrowArgs_ext ();
exampleArgs =
  EscrowArgs_ext
    (SemanticsTypes.Constant (Arith.Int_of_integer (10 :: Integer)))
    (SemanticsTypes.Token (Str.implode []) (Str.implode [])) buyer seller
    mediator (Arith.Int_of_integer (1664812800000 :: Integer))
    (Arith.Int_of_integer (1664816400000 :: Integer))
    (Arith.Int_of_integer (1664820420000 :: Integer))
    (Arith.Int_of_integer (1664824440000 :: Integer)) ();

escrowExample :: SemanticsTypes.Contract;
escrowExample = escrow exampleArgs;

confirmClaimPayments :: [Semantics.Payment];
confirmClaimPayments =
  [Semantics.Payment seller (SemanticsTypes.Account buyer) (token exampleArgs)
     (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment buyer (SemanticsTypes.Party buyer) (token exampleArgs)
      (Arith.Int_of_integer (10 :: Integer))];

dismissClaimPayments :: [Semantics.Payment];
dismissClaimPayments =
  [Semantics.Payment seller (SemanticsTypes.Account buyer) (token exampleArgs)
     (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment buyer (SemanticsTypes.Account seller) (token exampleArgs)
      (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment seller (SemanticsTypes.Party seller) (token exampleArgs)
      (Arith.Int_of_integer (10 :: Integer))];

confirmProblemPayments :: [Semantics.Payment];
confirmProblemPayments =
  [Semantics.Payment seller (SemanticsTypes.Account buyer) (token exampleArgs)
     (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment buyer (SemanticsTypes.Party buyer) (token exampleArgs)
      (Arith.Int_of_integer (10 :: Integer))];

confirmClaimTransactions :: [Semantics.Transaction_ext ()];
confirmClaimTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit seller buyer (token exampleArgs)
        (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char False True False False True False True False,
               Str.Char True False True False False True True False,
               Str.Char False False False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False True True True False,
               Str.Char False False True False True True True False,
               Str.Char False False False False False True False False,
               Str.Char False False False False True True True False,
               Str.Char False True False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False True False False True True False,
               Str.Char True False True True False True True False])
           buyer)
         Arith.one_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664817400000 :: Integer),
        Arith.Int_of_integer (1664817400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char False False True False False False True False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char False False False False True True True False,
               Str.Char True False True False True True True False,
               Str.Char False False True False True True True False,
               Str.Char True False True False False True True False,
               Str.Char False False False False False True False False,
               Str.Char False False False False True True True False,
               Str.Char False True False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False True False False True True False,
               Str.Char True False True True False True True False])
           seller)
         Arith.zero_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664821400000 :: Integer),
        Arith.Int_of_integer (1664822400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char True True False False False False True False,
               Str.Char True True True True False True True False,
               Str.Char False True True True False True True False,
               Str.Char False True True False False True True False,
               Str.Char True False False True False True True False,
               Str.Char False True False False True True True False,
               Str.Char True False True True False True True False,
               Str.Char False False False False False True False False,
               Str.Char True True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False False False False True True False,
               Str.Char True False False True False True True False,
               Str.Char True False True True False True True False])
           mediator)
         Arith.one_int]
      ()];

dismissClaimTransactions :: [Semantics.Transaction_ext ()];
dismissClaimTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit seller buyer (token exampleArgs)
        (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char False True False False True False True False,
               Str.Char True False True False False True True False,
               Str.Char False False False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False True True True False,
               Str.Char False False True False True True True False,
               Str.Char False False False False False True False False,
               Str.Char False False False False True True True False,
               Str.Char False True False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False True False False True True False,
               Str.Char True False True True False True True False])
           buyer)
         Arith.one_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664817400000 :: Integer),
        Arith.Int_of_integer (1664817400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char False False True False False False True False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char False False False False True True True False,
               Str.Char True False True False True True True False,
               Str.Char False False True False True True True False,
               Str.Char True False True False False True True False,
               Str.Char False False False False False True False False,
               Str.Char False False False False True True True False,
               Str.Char False True False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False True False False True True False,
               Str.Char True False True True False True True False])
           seller)
         Arith.zero_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664821400000 :: Integer),
        Arith.Int_of_integer (1664822400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char False False True False False False True False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char True False True True False True True False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char True True False False True True True False,
               Str.Char False False False False False True False False,
               Str.Char True True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False False False False True True False,
               Str.Char True False False True False True True False,
               Str.Char True False True True False True True False])
           mediator)
         Arith.zero_int]
      ()];

confirmProblemTransactions :: [Semantics.Transaction_ext ()];
confirmProblemTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit seller buyer (token exampleArgs)
        (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char False True False False True False True False,
               Str.Char True False True False False True True False,
               Str.Char False False False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False True True True False,
               Str.Char False False True False True True True False,
               Str.Char False False False False False True False False,
               Str.Char False False False False True True True False,
               Str.Char False True False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False True False False True True False,
               Str.Char True False True True False True True False])
           buyer)
         Arith.one_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664817400000 :: Integer),
        Arith.Int_of_integer (1664817400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char True True False False False False True False,
               Str.Char True True True True False True True False,
               Str.Char False True True True False True True False,
               Str.Char False True True False False True True False,
               Str.Char True False False True False True True False,
               Str.Char False True False False True True True False,
               Str.Char True False True True False True True False,
               Str.Char False False False False False True False False,
               Str.Char False False False False True True True False,
               Str.Char False True False False True True True False,
               Str.Char True True True True False True True False,
               Str.Char False True False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char True False True False False True True False,
               Str.Char True False True True False True True False])
           seller)
         Arith.one_int]
      ()];

everythingIsAlrightPayments :: [Semantics.Payment];
everythingIsAlrightPayments =
  [Semantics.Payment seller (SemanticsTypes.Party seller) (token exampleArgs)
     (Arith.Int_of_integer (10 :: Integer))];

everythingIsAlrightTransactions :: [Semantics.Transaction_ext ()];
everythingIsAlrightTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit seller buyer (token exampleArgs)
        (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Str.implode
             [Str.Char True False True False False False True False,
               Str.Char False True True False True True True False,
               Str.Char True False True False False True True False,
               Str.Char False True False False True True True False,
               Str.Char True False False True True True True False,
               Str.Char False False True False True True True False,
               Str.Char False False False True False True True False,
               Str.Char True False False True False True True False,
               Str.Char False True True True False True True False,
               Str.Char True True True False False True True False,
               Str.Char False False False False False True False False,
               Str.Char True False False True False True True False,
               Str.Char True True False False True True True False,
               Str.Char False False False False False True False False,
               Str.Char True False False False False True True False,
               Str.Char False False True True False True True False,
               Str.Char False True False False True True True False,
               Str.Char True False False True False True True False,
               Str.Char True True True False False True True False,
               Str.Char False False False True False True True False,
               Str.Char False False True False True True True False])
           buyer)
         Arith.zero_int]
      ()];

}
