{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Semantics(Payment(..), ReduceEffect, ReduceWarning, ReduceResult,
             TransactionWarning(..), ApplyAllResult, ReduceStepResult,
             TransactionError(..), TransactionOutputRecord_ext,
             TransactionOutput(..), Transaction_ext(..), evalValue,
             evalObservation, txOutWarnings, txOutPayments, reductionLoop,
             reduceContractUntilQuiescent, applyAllInputs, computeTransaction,
             playTrace, getOutcomes, maxTimeContract, getSignatures,
             calculateNonAmbiguousInterval, equal_Payment, txOutState,
             txOutContract, equal_TransactionWarning)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified OptBoundTimeInterval;
import qualified List;
import qualified Orderings;
import qualified Option;
import qualified MList;
import qualified HOL;
import qualified Product_Lexorder;
import qualified Product_Type;
import qualified ListTools;
import qualified SList;
import qualified SemanticsGuarantees;
import qualified SemanticsTypes;
import qualified Arith;

data Payment =
  Payment SemanticsTypes.Party SemanticsTypes.Payee SemanticsTypes.Token
    Arith.Int
  deriving (Prelude.Read, Prelude.Show);

data ApplyWarning = ApplyNoWarning
  | ApplyNonPositiveDeposit SemanticsTypes.Party SemanticsTypes.Party
      SemanticsTypes.Token Arith.Int
  deriving (Prelude.Read, Prelude.Show);

data ApplyResult =
  Applied ApplyWarning (SemanticsTypes.State_ext ()) SemanticsTypes.Contract
  | ApplyNoMatchError deriving (Prelude.Read, Prelude.Show);

data ReduceEffect = ReduceNoPayment | ReduceWithPayment Payment
  deriving (Prelude.Read, Prelude.Show);

data ReduceWarning = ReduceNoWarning
  | ReduceNonPositivePay SemanticsTypes.Party SemanticsTypes.Payee
      SemanticsTypes.Token Arith.Int
  | ReducePartialPay SemanticsTypes.Party SemanticsTypes.Payee
      SemanticsTypes.Token Arith.Int Arith.Int
  | ReduceShadowing SemanticsTypes.ValueId Arith.Int Arith.Int
  | ReduceAssertionFailed deriving (Prelude.Read, Prelude.Show);

data ReduceResult =
  ContractQuiescent Bool [ReduceWarning] [Payment] (SemanticsTypes.State_ext ())
    SemanticsTypes.Contract
  | RRAmbiguousTimeIntervalError deriving (Prelude.Read, Prelude.Show);

data TransactionWarning =
  TransactionNonPositiveDeposit SemanticsTypes.Party SemanticsTypes.Party
    SemanticsTypes.Token Arith.Int
  | TransactionNonPositivePay SemanticsTypes.Party SemanticsTypes.Payee
      SemanticsTypes.Token Arith.Int
  | TransactionPartialPay SemanticsTypes.Party SemanticsTypes.Payee
      SemanticsTypes.Token Arith.Int Arith.Int
  | TransactionShadowing SemanticsTypes.ValueId Arith.Int Arith.Int
  | TransactionAssertionFailed deriving (Prelude.Read, Prelude.Show);

data ApplyAllResult =
  ApplyAllSuccess Bool [TransactionWarning] [Payment]
    (SemanticsTypes.State_ext ()) SemanticsTypes.Contract
  | ApplyAllNoMatchError | ApplyAllAmbiguousTimeIntervalError
  deriving (Prelude.Read, Prelude.Show);

data ReduceStepResult =
  Reduced ReduceWarning ReduceEffect (SemanticsTypes.State_ext ())
    SemanticsTypes.Contract
  | NotReduced | AmbiguousTimeIntervalReductionError
  deriving (Prelude.Read, Prelude.Show);

data TransactionError = TEAmbiguousTimeIntervalError | TEApplyNoMatchError
  | TEIntervalError SemanticsTypes.IntervalError | TEUselessTransaction
  deriving (Prelude.Read, Prelude.Show);

data TransactionOutputRecord_ext a =
  TransactionOutputRecord_ext [TransactionWarning] [Payment]
    (SemanticsTypes.State_ext ()) SemanticsTypes.Contract a
  deriving (Prelude.Read, Prelude.Show);

data TransactionOutput = TransactionOutput (TransactionOutputRecord_ext ())
  | TransactionError TransactionError deriving (Prelude.Read, Prelude.Show);

data Transaction_ext a =
  Transaction_ext (Arith.Int, Arith.Int) [SemanticsTypes.Input] a
  deriving (Prelude.Read, Prelude.Show);

quot :: Arith.Int -> Arith.Int -> Arith.Int;
quot x y =
  (if Arith.less_int x Arith.zero_int == Arith.less_int y Arith.zero_int
    then Arith.divide_int x y
    else Arith.uminus_int
           (Arith.divide_int (Arith.abs_int x) (Arith.abs_int y)));

addSig ::
  [SemanticsTypes.Party] -> SemanticsTypes.Input -> [SemanticsTypes.Party];
addSig acc (SemanticsTypes.IDeposit uu p uv uw) = SList.insert p acc;
addSig acc (SemanticsTypes.IChoice (SemanticsTypes.ChoiceId ux p) uy) =
  SList.insert p acc;
addSig acc SemanticsTypes.INotify = acc;

gtIfNone :: Maybe Arith.Int -> Arith.Int -> Bool;
gtIfNone Nothing uu = True;
gtIfNone (Just x) y = Arith.less_int y x;

inBounds :: Arith.Int -> [(Arith.Int, Arith.Int)] -> Bool;
inBounds num =
  ListTools.anya
    (\ (l, u) -> Arith.less_eq_int l num && Arith.less_eq_int num u);

evalValue ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () -> SemanticsTypes.Value -> Arith.Int;
evalValue env state (SemanticsTypes.AvailableMoney accId token) =
  MList.findWithDefault Arith.zero_int (accId, token)
    (SemanticsTypes.accounts state);
evalValue env state (SemanticsTypes.Constant integer) = integer;
evalValue env state (SemanticsTypes.NegValue val) =
  Arith.uminus_int (evalValue env state val);
evalValue env state (SemanticsTypes.AddValue lhs rhs) =
  Arith.plus_int (evalValue env state lhs) (evalValue env state rhs);
evalValue env state (SemanticsTypes.SubValue lhs rhs) =
  Arith.minus_int (evalValue env state lhs) (evalValue env state rhs);
evalValue env state (SemanticsTypes.MulValue lhs rhs) =
  Arith.times_int (evalValue env state lhs) (evalValue env state rhs);
evalValue env state (SemanticsTypes.DivValue lhs rhs) =
  let {
    n = evalValue env state lhs;
    d = evalValue env state rhs;
  } in (if Arith.equal_int d Arith.zero_int then Arith.zero_int else quot n d);
evalValue env state (SemanticsTypes.ChoiceValue choId) =
  MList.findWithDefault Arith.zero_int choId (SemanticsTypes.choices state);
evalValue env state SemanticsTypes.TimeIntervalStart =
  fst (SemanticsTypes.timeInterval env);
evalValue env state SemanticsTypes.TimeIntervalEnd =
  snd (SemanticsTypes.timeInterval env);
evalValue env state (SemanticsTypes.UseValue valId) =
  MList.findWithDefault Arith.zero_int valId (SemanticsTypes.boundValues state);
evalValue env state (SemanticsTypes.Cond cond thn els) =
  (if evalObservation env state cond then evalValue env state thn
    else evalValue env state els);

evalObservation ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () -> SemanticsTypes.Observation -> Bool;
evalObservation env state (SemanticsTypes.AndObs lhs rhs) =
  evalObservation env state lhs && evalObservation env state rhs;
evalObservation env state (SemanticsTypes.OrObs lhs rhs) =
  evalObservation env state lhs || evalObservation env state rhs;
evalObservation env state (SemanticsTypes.NotObs subObs) =
  not (evalObservation env state subObs);
evalObservation env state (SemanticsTypes.ChoseSomething choId) =
  MList.member choId (SemanticsTypes.choices state);
evalObservation env state (SemanticsTypes.ValueGE lhs rhs) =
  Arith.less_eq_int (evalValue env state rhs) (evalValue env state lhs);
evalObservation env state (SemanticsTypes.ValueGT lhs rhs) =
  Arith.less_int (evalValue env state rhs) (evalValue env state lhs);
evalObservation env state (SemanticsTypes.ValueLT lhs rhs) =
  Arith.less_int (evalValue env state lhs) (evalValue env state rhs);
evalObservation env state (SemanticsTypes.ValueLE lhs rhs) =
  Arith.less_eq_int (evalValue env state lhs) (evalValue env state rhs);
evalObservation env state (SemanticsTypes.ValueEQ lhs rhs) =
  Arith.equal_int (evalValue env state lhs) (evalValue env state rhs);
evalObservation env state SemanticsTypes.TrueObs = True;
evalObservation env state SemanticsTypes.FalseObs = False;

updateMoneyInAccount ::
  SemanticsTypes.Party ->
    SemanticsTypes.Token ->
      Arith.Int ->
        [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] ->
          [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)];
updateMoneyInAccount accId token money accountsV =
  (if Arith.less_eq_int money Arith.zero_int
    then MList.delete (accId, token) accountsV
    else MList.insert (accId, token) money accountsV);

moneyInAccount ::
  SemanticsTypes.Party ->
    SemanticsTypes.Token ->
      [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] -> Arith.Int;
moneyInAccount accId token accountsV =
  MList.findWithDefault Arith.zero_int (accId, token) accountsV;

addMoneyToAccount ::
  SemanticsTypes.Party ->
    SemanticsTypes.Token ->
      Arith.Int ->
        [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] ->
          [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)];
addMoneyToAccount accId token money accountsV =
  let {
    balance = moneyInAccount accId token accountsV;
    newBalance = Arith.plus_int balance money;
  } in (if Arith.less_eq_int money Arith.zero_int then accountsV
         else updateMoneyInAccount accId token newBalance accountsV);

giveMoney ::
  SemanticsTypes.Party ->
    SemanticsTypes.Payee ->
      SemanticsTypes.Token ->
        Arith.Int ->
          [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] ->
            (ReduceEffect,
              [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)]);
giveMoney accountId payee token money accountsV =
  let {
    a = (case payee of {
          SemanticsTypes.Account accId ->
            addMoneyToAccount accId token money accountsV;
          SemanticsTypes.Party _ -> accountsV;
        });
  } in (ReduceWithPayment (Payment accountId payee token money), a);

txOutWarnings_update ::
  forall a.
    ([TransactionWarning] -> [TransactionWarning]) ->
      TransactionOutputRecord_ext a -> TransactionOutputRecord_ext a;
txOutWarnings_update txOutWarningsa
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = TransactionOutputRecord_ext (txOutWarningsa txOutWarnings) txOutPayments
      txOutState txOutContract more;

txOutPayments_update ::
  forall a.
    ([Payment] -> [Payment]) ->
      TransactionOutputRecord_ext a -> TransactionOutputRecord_ext a;
txOutPayments_update txOutPaymentsa
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = TransactionOutputRecord_ext txOutWarnings (txOutPaymentsa txOutPayments)
      txOutState txOutContract more;

txOutWarnings ::
  forall a. TransactionOutputRecord_ext a -> [TransactionWarning];
txOutWarnings
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutWarnings;

txOutPayments :: forall a. TransactionOutputRecord_ext a -> [Payment];
txOutPayments
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutPayments;

interval :: forall a. Transaction_ext a -> (Arith.Int, Arith.Int);
interval (Transaction_ext interval inputs more) = interval;

inputs :: forall a. Transaction_ext a -> [SemanticsTypes.Input];
inputs (Transaction_ext interval inputs more) = inputs;

equal_ReduceWarning :: ReduceWarning -> ReduceWarning -> Bool;
equal_ReduceWarning (ReduceShadowing x41 x42 x43) ReduceAssertionFailed = False;
equal_ReduceWarning ReduceAssertionFailed (ReduceShadowing x41 x42 x43) = False;
equal_ReduceWarning (ReducePartialPay x31 x32 x33 x34 x35) ReduceAssertionFailed
  = False;
equal_ReduceWarning ReduceAssertionFailed (ReducePartialPay x31 x32 x33 x34 x35)
  = False;
equal_ReduceWarning (ReducePartialPay x31 x32 x33 x34 x35)
  (ReduceShadowing x41 x42 x43) = False;
equal_ReduceWarning (ReduceShadowing x41 x42 x43)
  (ReducePartialPay x31 x32 x33 x34 x35) = False;
equal_ReduceWarning (ReduceNonPositivePay x21 x22 x23 x24) ReduceAssertionFailed
  = False;
equal_ReduceWarning ReduceAssertionFailed (ReduceNonPositivePay x21 x22 x23 x24)
  = False;
equal_ReduceWarning (ReduceNonPositivePay x21 x22 x23 x24)
  (ReduceShadowing x41 x42 x43) = False;
equal_ReduceWarning (ReduceShadowing x41 x42 x43)
  (ReduceNonPositivePay x21 x22 x23 x24) = False;
equal_ReduceWarning (ReduceNonPositivePay x21 x22 x23 x24)
  (ReducePartialPay x31 x32 x33 x34 x35) = False;
equal_ReduceWarning (ReducePartialPay x31 x32 x33 x34 x35)
  (ReduceNonPositivePay x21 x22 x23 x24) = False;
equal_ReduceWarning ReduceNoWarning ReduceAssertionFailed = False;
equal_ReduceWarning ReduceAssertionFailed ReduceNoWarning = False;
equal_ReduceWarning ReduceNoWarning (ReduceShadowing x41 x42 x43) = False;
equal_ReduceWarning (ReduceShadowing x41 x42 x43) ReduceNoWarning = False;
equal_ReduceWarning ReduceNoWarning (ReducePartialPay x31 x32 x33 x34 x35) =
  False;
equal_ReduceWarning (ReducePartialPay x31 x32 x33 x34 x35) ReduceNoWarning =
  False;
equal_ReduceWarning ReduceNoWarning (ReduceNonPositivePay x21 x22 x23 x24) =
  False;
equal_ReduceWarning (ReduceNonPositivePay x21 x22 x23 x24) ReduceNoWarning =
  False;
equal_ReduceWarning (ReduceShadowing x41 x42 x43) (ReduceShadowing y41 y42 y43)
  = SemanticsTypes.equal_ValueId x41 y41 &&
      Arith.equal_int x42 y42 && Arith.equal_int x43 y43;
equal_ReduceWarning (ReducePartialPay x31 x32 x33 x34 x35)
  (ReducePartialPay y31 y32 y33 y34 y35) =
  SemanticsTypes.equal_Party x31 y31 &&
    SemanticsTypes.equal_Payee x32 y32 &&
      SemanticsTypes.equal_Token x33 y33 &&
        Arith.equal_int x34 y34 && Arith.equal_int x35 y35;
equal_ReduceWarning (ReduceNonPositivePay x21 x22 x23 x24)
  (ReduceNonPositivePay y21 y22 y23 y24) =
  SemanticsTypes.equal_Party x21 y21 &&
    SemanticsTypes.equal_Payee x22 y22 &&
      SemanticsTypes.equal_Token x23 y23 && Arith.equal_int x24 y24;
equal_ReduceWarning ReduceAssertionFailed ReduceAssertionFailed = True;
equal_ReduceWarning ReduceNoWarning ReduceNoWarning = True;

refundOne ::
  [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] ->
    Maybe ((SemanticsTypes.Party, (SemanticsTypes.Token, Arith.Int)),
            [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)]);
refundOne (((accId, tok), money) : rest) =
  (if Arith.less_int Arith.zero_int money
    then Just ((accId, (tok, money)), rest) else refundOne rest);
refundOne [] = Nothing;

reduceContractStep ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () -> SemanticsTypes.Contract -> ReduceStepResult;
reduceContractStep uu state SemanticsTypes.Close =
  (case refundOne (SemanticsTypes.accounts state) of {
    Nothing -> NotReduced;
    Just ((party, (token, money)), newAccount) ->
      let {
        newState = SemanticsTypes.accounts_update (\ _ -> newAccount) state;
      } in Reduced ReduceNoWarning
             (ReduceWithPayment
               (Payment party (SemanticsTypes.Party party) token money))
             newState SemanticsTypes.Close;
  });
reduceContractStep env state (SemanticsTypes.Pay accId payee token val cont) =
  let {
    moneyToPay = evalValue env state val;
  } in (if Arith.less_eq_int moneyToPay Arith.zero_int
         then let {
                warning = ReduceNonPositivePay accId payee token moneyToPay;
              } in Reduced warning ReduceNoPayment state cont
         else let {
                balance =
                  moneyInAccount accId token (SemanticsTypes.accounts state);
                paidMoney = Orderings.min balance moneyToPay;
                newBalance = Arith.minus_int balance paidMoney;
                newAccs =
                  updateMoneyInAccount accId token newBalance
                    (SemanticsTypes.accounts state);
                warning =
                  (if Arith.less_int paidMoney moneyToPay
                    then ReducePartialPay accId payee token paidMoney moneyToPay
                    else ReduceNoWarning);
              } in (case giveMoney accId payee token paidMoney newAccs of {
                     (payment, finalAccs) ->
                       Reduced warning payment
                         (SemanticsTypes.accounts_update (\ _ -> finalAccs)
                           state)
                         cont;
                   }));
reduceContractStep env state (SemanticsTypes.If obs cont1 cont2) =
  let {
    a = (if evalObservation env state obs then cont1 else cont2);
  } in Reduced ReduceNoWarning ReduceNoPayment state a;
reduceContractStep env state (SemanticsTypes.When uv timeout cont) =
  (case SemanticsTypes.timeInterval env of {
    (startTime, endTime) ->
      (if Arith.less_int endTime timeout then NotReduced
        else (if Arith.less_eq_int timeout startTime
               then Reduced ReduceNoWarning ReduceNoPayment state cont
               else AmbiguousTimeIntervalReductionError));
  });
reduceContractStep env state (SemanticsTypes.Let valId val cont) =
  let {
    evaluatedValue = evalValue env state val;
    boundVals = SemanticsTypes.boundValues state;
    newState =
      SemanticsTypes.boundValues_update
        (\ _ -> MList.insert valId evaluatedValue boundVals) state;
    warn = (case MList.lookup valId boundVals of {
             Nothing -> ReduceNoWarning;
             Just oldVal -> ReduceShadowing valId oldVal evaluatedValue;
           });
  } in Reduced warn ReduceNoPayment newState cont;
reduceContractStep env state (SemanticsTypes.Assert obs cont) =
  let {
    warning =
      (if evalObservation env state obs then ReduceNoWarning
        else ReduceAssertionFailed);
  } in Reduced warning ReduceNoPayment state cont;

reductionLoop ::
  Bool ->
    SemanticsTypes.Environment_ext () ->
      SemanticsTypes.State_ext () ->
        SemanticsTypes.Contract -> [ReduceWarning] -> [Payment] -> ReduceResult;
reductionLoop reduced env state contract warnings payments =
  (case reduceContractStep env state contract of {
    Reduced warning effect newState ncontract ->
      let {
        newWarnings =
          (if equal_ReduceWarning warning ReduceNoWarning then warnings
            else warning : warnings);
        a = (case effect of {
              ReduceNoPayment -> payments;
              ReduceWithPayment payment -> payment : payments;
            });
      } in reductionLoop True env newState ncontract newWarnings a;
    NotReduced ->
      ContractQuiescent reduced (reverse warnings) (reverse payments) state
        contract;
    AmbiguousTimeIntervalReductionError -> RRAmbiguousTimeIntervalError;
  });

reduceContractUntilQuiescent ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () -> SemanticsTypes.Contract -> ReduceResult;
reduceContractUntilQuiescent env state contract =
  reductionLoop False env state contract [] [];

convertReduceWarnings :: [ReduceWarning] -> [TransactionWarning];
convertReduceWarnings [] = [];
convertReduceWarnings (ReduceNoWarning : rest) = convertReduceWarnings rest;
convertReduceWarnings (ReduceNonPositivePay accId payee tok amount : rest) =
  TransactionNonPositivePay accId payee tok amount : convertReduceWarnings rest;
convertReduceWarnings (ReducePartialPay accId payee tok paid expected : rest) =
  TransactionPartialPay accId payee tok paid expected :
    convertReduceWarnings rest;
convertReduceWarnings (ReduceShadowing valId oldVal newVal : rest) =
  TransactionShadowing valId oldVal newVal : convertReduceWarnings rest;
convertReduceWarnings (ReduceAssertionFailed : rest) =
  TransactionAssertionFailed : convertReduceWarnings rest;

convertApplyWarning :: ApplyWarning -> [TransactionWarning];
convertApplyWarning ApplyNoWarning = [];
convertApplyWarning (ApplyNonPositiveDeposit party accId tok amount) =
  [TransactionNonPositiveDeposit party accId tok amount];

applyCases ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () ->
      SemanticsTypes.Input -> [SemanticsTypes.Case] -> ApplyResult;
applyCases env state (SemanticsTypes.IDeposit accId1 party1 tok1 amount)
  (SemanticsTypes.Case (SemanticsTypes.Deposit accId2 party2 tok2 val) cont :
    rest)
  = (if SemanticsTypes.equal_Party accId1 accId2 &&
          SemanticsTypes.equal_Party party1 party2 &&
            SemanticsTypes.equal_Token tok1 tok2 &&
              Arith.equal_int amount (evalValue env state val)
      then let {
             warning =
               (if Arith.less_int Arith.zero_int amount then ApplyNoWarning
                 else ApplyNonPositiveDeposit party1 accId2 tok2 amount);
             newState =
               SemanticsTypes.accounts_update
                 (\ _ ->
                   addMoneyToAccount accId1 tok1 amount
                     (SemanticsTypes.accounts state))
                 state;
           } in Applied warning newState cont
      else applyCases env state
             (SemanticsTypes.IDeposit accId1 party1 tok1 amount) rest);
applyCases env state (SemanticsTypes.IChoice choId1 choice)
  (SemanticsTypes.Case (SemanticsTypes.Choice choId2 bounds) cont : rest) =
  (if SemanticsTypes.equal_ChoiceId choId1 choId2 && inBounds choice bounds
    then let {
           newState =
             SemanticsTypes.choices_update
               (\ _ ->
                 MList.insert choId1 choice (SemanticsTypes.choices state))
               state;
         } in Applied ApplyNoWarning newState cont
    else applyCases env state (SemanticsTypes.IChoice choId1 choice) rest);
applyCases env state SemanticsTypes.INotify
  (SemanticsTypes.Case (SemanticsTypes.Notify obs) cont : rest) =
  (if evalObservation env state obs then Applied ApplyNoWarning state cont
    else applyCases env state SemanticsTypes.INotify rest);
applyCases env state (SemanticsTypes.IDeposit accId1 party1 tok1 amount)
  (SemanticsTypes.Case (SemanticsTypes.Choice vb vc) va : rest) =
  applyCases env state (SemanticsTypes.IDeposit accId1 party1 tok1 amount) rest;
applyCases env state (SemanticsTypes.IDeposit accId1 party1 tok1 amount)
  (SemanticsTypes.Case (SemanticsTypes.Notify vb) va : rest) =
  applyCases env state (SemanticsTypes.IDeposit accId1 party1 tok1 amount) rest;
applyCases env state (SemanticsTypes.IChoice choId1 choice)
  (SemanticsTypes.Case (SemanticsTypes.Deposit vb vc vd ve) va : rest) =
  applyCases env state (SemanticsTypes.IChoice choId1 choice) rest;
applyCases env state (SemanticsTypes.IChoice choId1 choice)
  (SemanticsTypes.Case (SemanticsTypes.Notify vb) va : rest) =
  applyCases env state (SemanticsTypes.IChoice choId1 choice) rest;
applyCases env state SemanticsTypes.INotify
  (SemanticsTypes.Case (SemanticsTypes.Deposit vb vc vd ve) va : rest) =
  applyCases env state SemanticsTypes.INotify rest;
applyCases env state SemanticsTypes.INotify
  (SemanticsTypes.Case (SemanticsTypes.Choice vb vc) va : rest) =
  applyCases env state SemanticsTypes.INotify rest;
applyCases env state acc [] = ApplyNoMatchError;

applyInput ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () ->
      SemanticsTypes.Input -> SemanticsTypes.Contract -> ApplyResult;
applyInput env state input (SemanticsTypes.When cases t cont) =
  applyCases env state input cases;
applyInput env state input SemanticsTypes.Close = ApplyNoMatchError;
applyInput env state input (SemanticsTypes.Pay v va vb vc vd) =
  ApplyNoMatchError;
applyInput env state input (SemanticsTypes.If v va vb) = ApplyNoMatchError;
applyInput env state input (SemanticsTypes.Let v va vb) = ApplyNoMatchError;
applyInput env state input (SemanticsTypes.Assert v va) = ApplyNoMatchError;

applyAllLoop ::
  Bool ->
    SemanticsTypes.Environment_ext () ->
      SemanticsTypes.State_ext () ->
        SemanticsTypes.Contract ->
          [SemanticsTypes.Input] ->
            [TransactionWarning] -> [Payment] -> ApplyAllResult;
applyAllLoop contractChanged env state contract inputs warnings payments =
  (case reduceContractUntilQuiescent env state contract of {
    ContractQuiescent reduced reduceWarns pays curState cont ->
      (case inputs of {
        [] -> ApplyAllSuccess (contractChanged || reduced)
                (warnings ++ convertReduceWarnings reduceWarns)
                (payments ++ pays) curState cont;
        input : rest ->
          (case applyInput env curState input cont of {
            Applied applyWarn newState conta ->
              applyAllLoop True env newState conta rest
                (warnings ++
                  convertReduceWarnings reduceWarns ++
                    convertApplyWarning applyWarn)
                (payments ++ pays);
            ApplyNoMatchError -> ApplyAllNoMatchError;
          });
      });
    RRAmbiguousTimeIntervalError -> ApplyAllAmbiguousTimeIntervalError;
  });

applyAllInputs ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () ->
      SemanticsTypes.Contract -> [SemanticsTypes.Input] -> ApplyAllResult;
applyAllInputs env state contract inputs =
  applyAllLoop False env state contract inputs [] [];

fixInterval ::
  (Arith.Int, Arith.Int) ->
    SemanticsTypes.State_ext () -> SemanticsTypes.IntervalResult;
fixInterval (low, high) state =
  let {
    curMinTime = SemanticsTypes.minTime state;
    newLow = Orderings.max low curMinTime;
    curInterval = (newLow, high);
    env = SemanticsTypes.Environment_ext curInterval ();
    newState = SemanticsTypes.minTime_update (\ _ -> newLow) state;
  } in (if Arith.less_int high low
         then SemanticsTypes.IntervalError
                (SemanticsTypes.InvalidInterval (low, high))
         else (if Arith.less_int high curMinTime
                then SemanticsTypes.IntervalError
                       (SemanticsTypes.IntervalInPastError curMinTime
                         (low, high))
                else SemanticsTypes.IntervalTrimmed env newState));

computeTransaction ::
  Transaction_ext () ->
    SemanticsTypes.State_ext () -> SemanticsTypes.Contract -> TransactionOutput;
computeTransaction tx state contract =
  let {
    inps = inputs tx;
  } in (case fixInterval (interval tx) state of {
         SemanticsTypes.IntervalTrimmed env fixSta ->
           (case applyAllInputs env fixSta contract inps of {
             ApplyAllSuccess reduced warnings payments newState cont ->
               (if not reduced &&
                     (not (SemanticsTypes.equal_Contract contract
                            SemanticsTypes.Close) ||
                       null (SemanticsTypes.accounts state))
                 then TransactionError TEUselessTransaction
                 else TransactionOutput
                        (TransactionOutputRecord_ext warnings payments newState
                          cont ()));
             ApplyAllNoMatchError -> TransactionError TEApplyNoMatchError;
             ApplyAllAmbiguousTimeIntervalError ->
               TransactionError TEAmbiguousTimeIntervalError;
           });
         SemanticsTypes.IntervalError errora ->
           TransactionError (TEIntervalError errora);
       });

playTraceAux ::
  TransactionOutputRecord_ext () -> [Transaction_ext ()] -> TransactionOutput;
playTraceAux res [] = TransactionOutput res;
playTraceAux (TransactionOutputRecord_ext warnings payments state cont ())
  (h : t) =
  let {
    transRes = computeTransaction h state cont;
  } in (case transRes of {
         TransactionOutput transResRec ->
           playTraceAux
             (txOutWarnings_update
               (\ _ -> warnings ++ txOutWarnings transResRec)
               (txOutPayments_update
                 (\ _ -> payments ++ txOutPayments transResRec) transResRec))
             t;
         TransactionError _ -> transRes;
       });

emptyState :: Arith.Int -> SemanticsTypes.State_ext ();
emptyState sl =
  SemanticsTypes.State_ext MList.empty MList.empty MList.empty sl ();

playTrace ::
  Arith.Int ->
    SemanticsTypes.Contract -> [Transaction_ext ()] -> TransactionOutput;
playTrace sl c t =
  playTraceAux (TransactionOutputRecord_ext [] [] (emptyState sl) c ()) t;

subIfSome :: Maybe Arith.Int -> Arith.Int -> Maybe Arith.Int;
subIfSome Nothing uu = Nothing;
subIfSome (Just x) y = Just (Arith.minus_int x y);

addOutcome ::
  SemanticsTypes.Party ->
    Arith.Int ->
      [(SemanticsTypes.Party, Arith.Int)] ->
        [(SemanticsTypes.Party, Arith.Int)];
addOutcome party diffValue trOut =
  let {
    newValue = (case MList.lookup party trOut of {
                 Nothing -> diffValue;
                 Just value -> Arith.plus_int value diffValue;
               });
  } in MList.insert party newValue trOut;

getPartiesFromReduceEffect ::
  [ReduceEffect] -> [(SemanticsTypes.Party, (SemanticsTypes.Token, Arith.Int))];
getPartiesFromReduceEffect
  (ReduceWithPayment (Payment src (SemanticsTypes.Party p) tok m) : t) =
  (p, (tok, Arith.uminus_int m)) : getPartiesFromReduceEffect t;
getPartiesFromReduceEffect (ReduceNoPayment : t) = getPartiesFromReduceEffect t;
getPartiesFromReduceEffect
  (ReduceWithPayment (Payment va (SemanticsTypes.Account ve) vc vd) : t) =
  getPartiesFromReduceEffect t;
getPartiesFromReduceEffect [] = [];

getPartiesFromInput ::
  [SemanticsTypes.Input] ->
    [(SemanticsTypes.Party, (SemanticsTypes.Token, Arith.Int))];
getPartiesFromInput (SemanticsTypes.IDeposit uu p tok m : t) =
  (p, (tok, m)) : getPartiesFromInput t;
getPartiesFromInput (SemanticsTypes.IChoice v va : t) = getPartiesFromInput t;
getPartiesFromInput (SemanticsTypes.INotify : t) = getPartiesFromInput t;
getPartiesFromInput [] = [];

emptyOutcome :: [(SemanticsTypes.Party, Arith.Int)];
emptyOutcome = MList.empty;

getOutcomes ::
  [ReduceEffect] ->
    [SemanticsTypes.Input] -> [(SemanticsTypes.Party, Arith.Int)];
getOutcomes eff inp =
  List.foldl (\ acc (p, (_, m)) -> addOutcome p m acc) emptyOutcome
    (getPartiesFromReduceEffect eff ++ getPartiesFromInput inp);

maxTimeCase :: SemanticsTypes.Case -> Arith.Int;
maxTimeCase (SemanticsTypes.Case vc contract) = maxTimeContract contract;

maxTimeContract :: SemanticsTypes.Contract -> Arith.Int;
maxTimeContract SemanticsTypes.Close = Arith.zero_int;
maxTimeContract (SemanticsTypes.Pay uu uv uw ux contract) =
  maxTimeContract contract;
maxTimeContract (SemanticsTypes.If uy contractTrue contractFalse) =
  Orderings.max (maxTimeContract contractTrue) (maxTimeContract contractFalse);
maxTimeContract (SemanticsTypes.When [] timeout contract) =
  Orderings.max timeout (maxTimeContract contract);
maxTimeContract (SemanticsTypes.When (head : tail) timeout contract) =
  Orderings.max (maxTimeCase head)
    (maxTimeContract (SemanticsTypes.When tail timeout contract));
maxTimeContract (SemanticsTypes.Let uz va contract) = maxTimeContract contract;
maxTimeContract (SemanticsTypes.Assert vb contract) = maxTimeContract contract;

getSignatures :: [SemanticsTypes.Input] -> [SemanticsTypes.Party];
getSignatures l = List.foldl addSig SList.empty l;

calculateNonAmbiguousInterval ::
  Maybe Arith.Int ->
    Arith.Int ->
      SemanticsTypes.Contract ->
        (OptBoundTimeInterval.BEndpoint, OptBoundTimeInterval.BEndpoint);
calculateNonAmbiguousInterval uu uv SemanticsTypes.Close =
  (OptBoundTimeInterval.Unbounded, OptBoundTimeInterval.Unbounded);
calculateNonAmbiguousInterval n t (SemanticsTypes.Pay uw ux uy uz c) =
  calculateNonAmbiguousInterval n t c;
calculateNonAmbiguousInterval n t (SemanticsTypes.If va ct cf) =
  OptBoundTimeInterval.intersectInterval (calculateNonAmbiguousInterval n t ct)
    (calculateNonAmbiguousInterval n t cf);
calculateNonAmbiguousInterval n t (SemanticsTypes.When [] timeout tcont) =
  (if Arith.less_int t timeout
    then (OptBoundTimeInterval.Unbounded,
           OptBoundTimeInterval.Bounded (Arith.minus_int timeout Arith.one_int))
    else OptBoundTimeInterval.intersectInterval
           (OptBoundTimeInterval.Bounded timeout,
             OptBoundTimeInterval.Unbounded)
           (calculateNonAmbiguousInterval n t tcont));
calculateNonAmbiguousInterval n t
  (SemanticsTypes.When (SemanticsTypes.Case vb cont : tail) timeout tcont) =
  (if gtIfNone n Arith.zero_int
    then OptBoundTimeInterval.intersectInterval
           (calculateNonAmbiguousInterval (subIfSome n Arith.one_int) t cont)
           (calculateNonAmbiguousInterval n t
             (SemanticsTypes.When tail timeout tcont))
    else calculateNonAmbiguousInterval n t
           (SemanticsTypes.When tail timeout tcont));
calculateNonAmbiguousInterval n t (SemanticsTypes.Let vc vd c) =
  calculateNonAmbiguousInterval n t c;
calculateNonAmbiguousInterval n t (SemanticsTypes.Assert ve c) =
  calculateNonAmbiguousInterval n t c;

equal_Payment :: Payment -> Payment -> Bool;
equal_Payment (Payment x1 x2 x3 x4) (Payment y1 y2 y3 y4) =
  SemanticsTypes.equal_Party x1 y1 &&
    SemanticsTypes.equal_Payee x2 y2 &&
      SemanticsTypes.equal_Token x3 y3 && Arith.equal_int x4 y4;

txOutState ::
  forall a. TransactionOutputRecord_ext a -> SemanticsTypes.State_ext ();
txOutState
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutState;

txOutContract ::
  forall a. TransactionOutputRecord_ext a -> SemanticsTypes.Contract;
txOutContract
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutContract;

equal_TransactionWarning :: TransactionWarning -> TransactionWarning -> Bool;
equal_TransactionWarning (TransactionShadowing x41 x42 x43)
  TransactionAssertionFailed = False;
equal_TransactionWarning TransactionAssertionFailed
  (TransactionShadowing x41 x42 x43) = False;
equal_TransactionWarning (TransactionPartialPay x31 x32 x33 x34 x35)
  TransactionAssertionFailed = False;
equal_TransactionWarning TransactionAssertionFailed
  (TransactionPartialPay x31 x32 x33 x34 x35) = False;
equal_TransactionWarning (TransactionPartialPay x31 x32 x33 x34 x35)
  (TransactionShadowing x41 x42 x43) = False;
equal_TransactionWarning (TransactionShadowing x41 x42 x43)
  (TransactionPartialPay x31 x32 x33 x34 x35) = False;
equal_TransactionWarning (TransactionNonPositivePay x21 x22 x23 x24)
  TransactionAssertionFailed = False;
equal_TransactionWarning TransactionAssertionFailed
  (TransactionNonPositivePay x21 x22 x23 x24) = False;
equal_TransactionWarning (TransactionNonPositivePay x21 x22 x23 x24)
  (TransactionShadowing x41 x42 x43) = False;
equal_TransactionWarning (TransactionShadowing x41 x42 x43)
  (TransactionNonPositivePay x21 x22 x23 x24) = False;
equal_TransactionWarning (TransactionNonPositivePay x21 x22 x23 x24)
  (TransactionPartialPay x31 x32 x33 x34 x35) = False;
equal_TransactionWarning (TransactionPartialPay x31 x32 x33 x34 x35)
  (TransactionNonPositivePay x21 x22 x23 x24) = False;
equal_TransactionWarning (TransactionNonPositiveDeposit x11 x12 x13 x14)
  TransactionAssertionFailed = False;
equal_TransactionWarning TransactionAssertionFailed
  (TransactionNonPositiveDeposit x11 x12 x13 x14) = False;
equal_TransactionWarning (TransactionNonPositiveDeposit x11 x12 x13 x14)
  (TransactionShadowing x41 x42 x43) = False;
equal_TransactionWarning (TransactionShadowing x41 x42 x43)
  (TransactionNonPositiveDeposit x11 x12 x13 x14) = False;
equal_TransactionWarning (TransactionNonPositiveDeposit x11 x12 x13 x14)
  (TransactionPartialPay x31 x32 x33 x34 x35) = False;
equal_TransactionWarning (TransactionPartialPay x31 x32 x33 x34 x35)
  (TransactionNonPositiveDeposit x11 x12 x13 x14) = False;
equal_TransactionWarning (TransactionNonPositiveDeposit x11 x12 x13 x14)
  (TransactionNonPositivePay x21 x22 x23 x24) = False;
equal_TransactionWarning (TransactionNonPositivePay x21 x22 x23 x24)
  (TransactionNonPositiveDeposit x11 x12 x13 x14) = False;
equal_TransactionWarning (TransactionShadowing x41 x42 x43)
  (TransactionShadowing y41 y42 y43) =
  SemanticsTypes.equal_ValueId x41 y41 &&
    Arith.equal_int x42 y42 && Arith.equal_int x43 y43;
equal_TransactionWarning (TransactionPartialPay x31 x32 x33 x34 x35)
  (TransactionPartialPay y31 y32 y33 y34 y35) =
  SemanticsTypes.equal_Party x31 y31 &&
    SemanticsTypes.equal_Payee x32 y32 &&
      SemanticsTypes.equal_Token x33 y33 &&
        Arith.equal_int x34 y34 && Arith.equal_int x35 y35;
equal_TransactionWarning (TransactionNonPositivePay x21 x22 x23 x24)
  (TransactionNonPositivePay y21 y22 y23 y24) =
  SemanticsTypes.equal_Party x21 y21 &&
    SemanticsTypes.equal_Payee x22 y22 &&
      SemanticsTypes.equal_Token x23 y23 && Arith.equal_int x24 y24;
equal_TransactionWarning (TransactionNonPositiveDeposit x11 x12 x13 x14)
  (TransactionNonPositiveDeposit y11 y12 y13 y14) =
  SemanticsTypes.equal_Party x11 y11 &&
    SemanticsTypes.equal_Party x12 y12 &&
      SemanticsTypes.equal_Token x13 y13 && Arith.equal_int x14 y14;
equal_TransactionWarning TransactionAssertionFailed TransactionAssertionFailed =
  True;

}
