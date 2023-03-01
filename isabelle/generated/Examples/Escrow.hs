{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Examples.Escrow(EscrowArgs_ext, escrowExample, confirmClaimPayments,
                   dismissClaimPayments, confirmProblemPayments,
                   confirmClaimTransactions, dismissClaimTransactions,
                   confirmProblemTransactions, everythingIsAlrightPayments,
                   everythingIsAlrightTransactions)
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

data EscrowArgs_ext a =
  EscrowArgs_ext SemanticsTypes.Value SemanticsTypes.Token SemanticsTypes.Party
    SemanticsTypes.Party SemanticsTypes.Party Arith.Int Arith.Int Arith.Int
    Arith.Int a
  deriving (Prelude.Read, Prelude.Show);

paymentDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
paymentDeadline
  (EscrowArgs_ext price token seller buyer mediator paymentDeadline
    complaintDeadline disputeDeadline mediationDeadline more)
  = paymentDeadline;

seller :: forall a. EscrowArgs_ext a -> SemanticsTypes.Party;
seller
  (EscrowArgs_ext price token seller buyer mediator paymentDeadline
    complaintDeadline disputeDeadline mediationDeadline more)
  = seller;

price :: forall a. EscrowArgs_ext a -> SemanticsTypes.Value;
price (EscrowArgs_ext price token seller buyer mediator paymentDeadline
        complaintDeadline disputeDeadline mediationDeadline more)
  = price;

buyer :: forall a. EscrowArgs_ext a -> SemanticsTypes.Party;
buyer (EscrowArgs_ext price token seller buyer mediator paymentDeadline
        complaintDeadline disputeDeadline mediationDeadline more)
  = buyer;

adaToken :: SemanticsTypes.Token;
adaToken = SemanticsTypes.Token (Stringa.implode []) (Stringa.implode []);

complaintDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
complaintDeadline
  (EscrowArgs_ext price token seller buyer mediator paymentDeadline
    complaintDeadline disputeDeadline mediationDeadline more)
  = complaintDeadline;

disputeDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
disputeDeadline
  (EscrowArgs_ext price token seller buyer mediator paymentDeadline
    complaintDeadline disputeDeadline mediationDeadline more)
  = disputeDeadline;

mediationDeadline :: forall a. EscrowArgs_ext a -> Arith.Int;
mediationDeadline
  (EscrowArgs_ext price token seller buyer mediator paymentDeadline
    complaintDeadline disputeDeadline mediationDeadline more)
  = mediationDeadline;

mediator :: forall a. EscrowArgs_ext a -> SemanticsTypes.Party;
mediator
  (EscrowArgs_ext price token seller buyer mediator paymentDeadline
    complaintDeadline disputeDeadline mediationDeadline more)
  = mediator;

mediation :: EscrowArgs_ext () -> SemanticsTypes.Contract;
mediation args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Choice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char False False True False False False True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char True False True True False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char True True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False False False False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True False True True False True True False])
           (mediator args))
         [SemanticsTypes.Bound Arith.zero_int Arith.zero_int])
       (SemanticsTypes.Pay (buyer args) (SemanticsTypes.Account (seller args))
         adaToken (price args) SemanticsTypes.Close),
      SemanticsTypes.Case
        (SemanticsTypes.Choice
          (SemanticsTypes.ChoiceId
            (Stringa.implode
              [Stringa.Char True True False False False False True False,
                Stringa.Char True True True True False True True False,
                Stringa.Char False True True True False True True False,
                Stringa.Char False True True False False True True False,
                Stringa.Char True False False True False True True False,
                Stringa.Char False True False False True True True False,
                Stringa.Char True False True True False True True False,
                Stringa.Char False False False False False True False False,
                Stringa.Char True True False False False True True False,
                Stringa.Char False False True True False True True False,
                Stringa.Char True False False False False True True False,
                Stringa.Char True False False True False True True False,
                Stringa.Char True False True True False True True False])
            (mediator args))
          [SemanticsTypes.Bound Arith.one_int Arith.one_int])
        SemanticsTypes.Close]
    (mediationDeadline args) SemanticsTypes.Close;

dispute :: EscrowArgs_ext () -> SemanticsTypes.Contract;
dispute args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Choice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char True True False False False False True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True True True False True True False,
               Stringa.Char False True True False False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True False True True False True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char False False False False True True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char True False True True False True True False])
           (seller args))
         [SemanticsTypes.Bound Arith.one_int Arith.one_int])
       SemanticsTypes.Close,
      SemanticsTypes.Case
        (SemanticsTypes.Choice
          (SemanticsTypes.ChoiceId
            (Stringa.implode
              [Stringa.Char False False True False False False True False,
                Stringa.Char True False False True False True True False,
                Stringa.Char True True False False True True True False,
                Stringa.Char False False False False True True True False,
                Stringa.Char True False True False True True True False,
                Stringa.Char False False True False True True True False,
                Stringa.Char True False True False False True True False,
                Stringa.Char False False False False False True False False,
                Stringa.Char False False False False True True True False,
                Stringa.Char False True False False True True True False,
                Stringa.Char True True True True False True True False,
                Stringa.Char False True False False False True True False,
                Stringa.Char False False True True False True True False,
                Stringa.Char True False True False False True True False,
                Stringa.Char True False True True False True True False])
            (seller args))
          [SemanticsTypes.Bound Arith.zero_int Arith.zero_int])
        (mediation args)]
    (disputeDeadline args) SemanticsTypes.Close;

report :: EscrowArgs_ext () -> SemanticsTypes.Contract;
report args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Choice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char True False True False False False True False,
               Stringa.Char False True True False True True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True False False True True True True False,
               Stringa.Char False False True False True True True False,
               Stringa.Char False False False True False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char False True True True False True True False,
               Stringa.Char True True True False False True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char True False False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True True False False True True False,
               Stringa.Char False False False True False True True False,
               Stringa.Char False False True False True True True False])
           (buyer args))
         [SemanticsTypes.Bound Arith.zero_int Arith.zero_int])
       SemanticsTypes.Close,
      SemanticsTypes.Case
        (SemanticsTypes.Choice
          (SemanticsTypes.ChoiceId
            (Stringa.implode
              [Stringa.Char False True False False True False True False,
                Stringa.Char True False True False False True True False,
                Stringa.Char False False False False True True True False,
                Stringa.Char True True True True False True True False,
                Stringa.Char False True False False True True True False,
                Stringa.Char False False True False True True True False,
                Stringa.Char False False False False False True False False,
                Stringa.Char False False False False True True True False,
                Stringa.Char False True False False True True True False,
                Stringa.Char True True True True False True True False,
                Stringa.Char False True False False False True True False,
                Stringa.Char False False True True False True True False,
                Stringa.Char True False True False False True True False,
                Stringa.Char True False True True False True True False])
            (buyer args))
          [SemanticsTypes.Bound Arith.one_int Arith.one_int])
        (SemanticsTypes.Pay (seller args) (SemanticsTypes.Account (buyer args))
          adaToken (price args) (dispute args))]
    (complaintDeadline args) SemanticsTypes.Close;

escrow :: EscrowArgs_ext () -> SemanticsTypes.Contract;
escrow args =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Deposit (seller args) (buyer args) adaToken (price args))
       (report args)]
    (paymentDeadline args) SemanticsTypes.Close;

escrowArgs :: EscrowArgs_ext ();
escrowArgs =
  EscrowArgs_ext
    (SemanticsTypes.Constant (Arith.Int_of_integer (10 :: Integer))) adaToken
    (SemanticsTypes.Role
      (Stringa.implode
        [Stringa.Char True True False False True False True False,
          Stringa.Char True False True False False True True False,
          Stringa.Char False False True True False True True False,
          Stringa.Char False False True True False True True False,
          Stringa.Char True False True False False True True False,
          Stringa.Char False True False False True True True False]))
    (SemanticsTypes.Role
      (Stringa.implode
        [Stringa.Char False True False False False False True False,
          Stringa.Char True False True False True True True False,
          Stringa.Char True False False True True True True False,
          Stringa.Char True False True False False True True False,
          Stringa.Char False True False False True True True False]))
    (SemanticsTypes.Role
      (Stringa.implode
        [Stringa.Char True False True True False False True False,
          Stringa.Char True False True False False True True False,
          Stringa.Char False False True False False True True False,
          Stringa.Char True False False True False True True False,
          Stringa.Char True False False False False True True False,
          Stringa.Char False False True False True True True False,
          Stringa.Char True True True True False True True False,
          Stringa.Char False True False False True True True False]))
    (Arith.Int_of_integer (1664812800000 :: Integer))
    (Arith.Int_of_integer (1664816400000 :: Integer))
    (Arith.Int_of_integer (1664820420000 :: Integer))
    (Arith.Int_of_integer (1664824440000 :: Integer)) ();

escrowExample :: SemanticsTypes.Contract;
escrowExample = escrow escrowArgs;

token :: forall a. EscrowArgs_ext a -> SemanticsTypes.Token;
token (EscrowArgs_ext price token seller buyer mediator paymentDeadline
        complaintDeadline disputeDeadline mediationDeadline more)
  = token;

confirmClaimPayments :: [Semantics.Payment];
confirmClaimPayments =
  [Semantics.Payment (seller escrowArgs)
     (SemanticsTypes.Account (buyer escrowArgs)) (token escrowArgs)
     (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment (buyer escrowArgs)
      (SemanticsTypes.Party (buyer escrowArgs)) (token escrowArgs)
      (Arith.Int_of_integer (10 :: Integer))];

dismissClaimPayments :: [Semantics.Payment];
dismissClaimPayments =
  [Semantics.Payment (seller escrowArgs)
     (SemanticsTypes.Account (buyer escrowArgs)) (token escrowArgs)
     (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment (buyer escrowArgs)
      (SemanticsTypes.Account (seller escrowArgs)) (token escrowArgs)
      (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment (seller escrowArgs)
      (SemanticsTypes.Party (seller escrowArgs)) (token escrowArgs)
      (Arith.Int_of_integer (10 :: Integer))];

confirmProblemPayments :: [Semantics.Payment];
confirmProblemPayments =
  [Semantics.Payment (seller escrowArgs)
     (SemanticsTypes.Account (buyer escrowArgs)) (token escrowArgs)
     (Arith.Int_of_integer (10 :: Integer)),
    Semantics.Payment (buyer escrowArgs)
      (SemanticsTypes.Party (buyer escrowArgs)) (token escrowArgs)
      (Arith.Int_of_integer (10 :: Integer))];

confirmClaimTransactions :: [Semantics.Transaction_ext ()];
confirmClaimTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit (seller escrowArgs) (buyer escrowArgs)
        (token escrowArgs) (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char False True False False True False True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char False False False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char False False True False True True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char False False False False True True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char True False True True False True True False])
           (buyer escrowArgs))
         Arith.one_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664817400000 :: Integer),
        Arith.Int_of_integer (1664817400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char False False True False False False True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char False False False False True True True False,
               Stringa.Char True False True False True True True False,
               Stringa.Char False False True False True True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char False False False False True True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char True False True True False True True False])
           (seller escrowArgs))
         Arith.zero_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664821400000 :: Integer),
        Arith.Int_of_integer (1664822400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char True True False False False False True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True True True False True True False,
               Stringa.Char False True True False False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True False True True False True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char True True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False False False False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True False True True False True True False])
           (mediator escrowArgs))
         Arith.one_int]
      ()];

dismissClaimTransactions :: [Semantics.Transaction_ext ()];
dismissClaimTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit (seller escrowArgs) (buyer escrowArgs)
        (token escrowArgs) (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char False True False False True False True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char False False False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char False False True False True True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char False False False False True True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char True False True True False True True False])
           (buyer escrowArgs))
         Arith.one_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664817400000 :: Integer),
        Arith.Int_of_integer (1664817400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char False False True False False False True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char False False False False True True True False,
               Stringa.Char True False True False True True True False,
               Stringa.Char False False True False True True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char False False False False True True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char True False True True False True True False])
           (seller escrowArgs))
         Arith.zero_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664821400000 :: Integer),
        Arith.Int_of_integer (1664822400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char False False True False False False True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char True False True True False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char True True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False False False False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True False True True False True True False])
           (mediator escrowArgs))
         Arith.zero_int]
      ()];

confirmProblemTransactions :: [Semantics.Transaction_ext ()];
confirmProblemTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit (seller escrowArgs) (buyer escrowArgs)
        (token escrowArgs) (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char False True False False True False True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char False False False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char False False True False True True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char False False False False True True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char True False True True False True True False])
           (buyer escrowArgs))
         Arith.one_int]
      (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664817400000 :: Integer),
        Arith.Int_of_integer (1664817400000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char True True False False False False True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True True True False True True False,
               Stringa.Char False True True False False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True False True True False True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char False False False False True True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True True True True False True True False,
               Stringa.Char False True False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char True False True True False True True False])
           (seller escrowArgs))
         Arith.one_int]
      ()];

everythingIsAlrightPayments :: [Semantics.Payment];
everythingIsAlrightPayments =
  [Semantics.Payment (seller escrowArgs)
     (SemanticsTypes.Party (seller escrowArgs)) (token escrowArgs)
     (Arith.Int_of_integer (10 :: Integer))];

everythingIsAlrightTransactions :: [Semantics.Transaction_ext ()];
everythingIsAlrightTransactions =
  [Semantics.Transaction_ext
     (Arith.Int_of_integer (1664812600000 :: Integer),
       Arith.Int_of_integer (1664812700000 :: Integer))
     [SemanticsTypes.IDeposit (seller escrowArgs) (buyer escrowArgs)
        (token escrowArgs) (Arith.Int_of_integer (10 :: Integer))]
     (),
    Semantics.Transaction_ext
      (Arith.Int_of_integer (1664812900000 :: Integer),
        Arith.Int_of_integer (1664813100000 :: Integer))
      [SemanticsTypes.IChoice
         (SemanticsTypes.ChoiceId
           (Stringa.implode
             [Stringa.Char True False True False False False True False,
               Stringa.Char False True True False True True True False,
               Stringa.Char True False True False False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True False False True True True True False,
               Stringa.Char False False True False True True True False,
               Stringa.Char False False False True False True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char False True True True False True True False,
               Stringa.Char True True True False False True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True False False True True True False,
               Stringa.Char False False False False False True False False,
               Stringa.Char True False False False False True True False,
               Stringa.Char False False True True False True True False,
               Stringa.Char False True False False True True True False,
               Stringa.Char True False False True False True True False,
               Stringa.Char True True True False False True True False,
               Stringa.Char False False False True False True True False,
               Stringa.Char False False True False True True True False])
           (buyer escrowArgs))
         Arith.zero_int]
      ()];

}
