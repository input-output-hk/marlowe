{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Semantics(ReduceWarning, ReduceEffect, ReduceResult, ApplyAllResult,
             IntervalResult, ReduceStepResult, evalValue, evalObservation,
             reductionLoop, reduceContractUntilQuiescent, applyAllInputs,
             computeTransaction, playTrace, getOutcomes, isQuiescent,
             maxTimeContract, getSignatures, equal_ReduceResult)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified List;
import qualified Orderings;
import qualified Product_Lexorder;
import qualified Option;
import qualified MList;
import qualified Division;
import qualified HOL;
import qualified SList;
import qualified SemanticsGuarantees;
import qualified Arith;
import qualified SemanticsTypes;

data ReduceWarning = ReduceNoWarning
  | ReduceNonPositivePay SemanticsTypes.Party SemanticsTypes.Payee
      SemanticsTypes.Token Arith.Int
  | ReducePartialPay SemanticsTypes.Party SemanticsTypes.Payee
      SemanticsTypes.Token Arith.Int Arith.Int
  | ReduceShadowing SemanticsTypes.ValueId Arith.Int Arith.Int
  | ReduceAssertionFailed deriving (Prelude.Read, Prelude.Show);

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

instance Eq ReduceWarning where {
  a == b = equal_ReduceWarning a b;
};

data ApplyWarning = ApplyNoWarning
  | ApplyNonPositiveDeposit SemanticsTypes.Party SemanticsTypes.Party
      SemanticsTypes.Token Arith.Int
  deriving (Prelude.Read, Prelude.Show);

data ApplyResult =
  Applied ApplyWarning (SemanticsTypes.State_ext ()) SemanticsTypes.Contract
  | ApplyNoMatchError deriving (Prelude.Read, Prelude.Show);

data ReduceEffect = ReduceNoPayment | ReduceWithPayment SemanticsTypes.Payment
  deriving (Prelude.Read, Prelude.Show);

data ReduceResult =
  ContractQuiescent Bool [ReduceWarning] [SemanticsTypes.Payment]
    (SemanticsTypes.State_ext ()) SemanticsTypes.Contract
  | RRAmbiguousTimeIntervalError deriving (Prelude.Read, Prelude.Show);

data ApplyAllResult =
  ApplyAllSuccess Bool [SemanticsTypes.TransactionWarning]
    [SemanticsTypes.Payment] (SemanticsTypes.State_ext ())
    SemanticsTypes.Contract
  | ApplyAllNoMatchError | ApplyAllAmbiguousTimeIntervalError
  deriving (Prelude.Read, Prelude.Show);

data IntervalResult =
  IntervalTrimmed (SemanticsTypes.Environment_ext ())
    (SemanticsTypes.State_ext ())
  | IntervalError SemanticsTypes.IntervalError
  deriving (Prelude.Read, Prelude.Show);

data ReduceStepResult =
  Reduced ReduceWarning ReduceEffect (SemanticsTypes.State_ext ())
    SemanticsTypes.Contract
  | NotReduced | AmbiguousTimeIntervalReductionError
  deriving (Prelude.Read, Prelude.Show);

addSig ::
  [SemanticsTypes.Party] -> SemanticsTypes.Input -> [SemanticsTypes.Party];
addSig acc (SemanticsTypes.IDeposit uu p uv uw) = SList.insert p acc;
addSig acc (SemanticsTypes.IChoice (SemanticsTypes.ChoiceId ux p) uy) =
  SList.insert p acc;
addSig acc SemanticsTypes.INotify = acc;

moneyInAccount ::
  SemanticsTypes.Party ->
    SemanticsTypes.Token ->
      [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] -> Arith.Int;
moneyInAccount accId token accountsV =
  MList.findWithDefault Arith.zero_int (accId, token) accountsV;

evalValue ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () -> SemanticsTypes.Value -> Arith.Int;
evalValue env state (SemanticsTypes.AvailableMoney accId token) =
  moneyInAccount accId token (SemanticsTypes.accounts state);
evalValue env state (SemanticsTypes.ChoiceValue choId) =
  MList.findWithDefault Arith.zero_int choId (SemanticsTypes.choices state);
evalValue env state (SemanticsTypes.UseValue valId) =
  MList.findWithDefault Arith.zero_int valId (SemanticsTypes.boundValues state);
evalValue env state (SemanticsTypes.Constant c) = c;
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
  } in (if Arith.equal_int d Arith.zero_int then Arith.zero_int
         else Division.quot n d);
evalValue env state SemanticsTypes.TimeIntervalStart =
  fst (SemanticsTypes.timeInterval env);
evalValue env state SemanticsTypes.TimeIntervalEnd =
  snd (SemanticsTypes.timeInterval env);
evalValue env state (SemanticsTypes.Cond cond thn els) =
  (if evalObservation env state cond then evalValue env state thn
    else evalValue env state els);

evalObservation ::
  SemanticsTypes.Environment_ext () ->
    SemanticsTypes.State_ext () -> SemanticsTypes.Observation -> Bool;
evalObservation env state SemanticsTypes.TrueObs = True;
evalObservation env state SemanticsTypes.FalseObs = False;
evalObservation env state (SemanticsTypes.NotObs subObs) =
  not (evalObservation env state subObs);
evalObservation env state (SemanticsTypes.AndObs lhs rhs) =
  evalObservation env state lhs && evalObservation env state rhs;
evalObservation env state (SemanticsTypes.OrObs lhs rhs) =
  evalObservation env state lhs || evalObservation env state rhs;
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

addMoneyToAccount ::
  SemanticsTypes.Party ->
    SemanticsTypes.Token ->
      Arith.Int ->
        [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] ->
          [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)];
addMoneyToAccount accId token money accts =
  let {
    balance = moneyInAccount accId token accts;
    newBalance = Arith.plus_int balance money;
  } in (if Arith.less_eq_int money Arith.zero_int then accts
         else updateMoneyInAccount accId token newBalance accts);

giveMoney ::
  SemanticsTypes.Party ->
    SemanticsTypes.Payee ->
      SemanticsTypes.Token ->
        Arith.Int ->
          [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] ->
            (ReduceEffect,
              [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)]);
giveMoney accountId payee token money accts =
  let {
    a = (case payee of {
          SemanticsTypes.Account accId ->
            addMoneyToAccount accId token money accts;
          SemanticsTypes.Party _ -> accts;
        });
  } in (ReduceWithPayment (SemanticsTypes.Payment accountId payee token money),
         a);

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
    Just ((party, (token, money)), newAccounts) ->
      let {
        newState = SemanticsTypes.accounts_update (\ _ -> newAccounts) state;
      } in Reduced ReduceNoWarning
             (ReduceWithPayment
               (SemanticsTypes.Payment party (SemanticsTypes.Party party) token
                 money))
             newState SemanticsTypes.Close;
  });
reduceContractStep env state (SemanticsTypes.Pay accId payee token val cont) =
  let {
    amountToPay = evalValue env state val;
  } in (if Arith.less_eq_int amountToPay Arith.zero_int
         then let {
                warning = ReduceNonPositivePay accId payee token amountToPay;
              } in Reduced warning ReduceNoPayment state cont
         else let {
                balance =
                  moneyInAccount accId token (SemanticsTypes.accounts state);
                paidAmount = Orderings.min balance amountToPay;
                newBalance = Arith.minus_int balance paidAmount;
                newAccs =
                  updateMoneyInAccount accId token newBalance
                    (SemanticsTypes.accounts state);
                warning =
                  (if Arith.less_int paidAmount amountToPay
                    then ReducePartialPay accId payee token paidAmount
                           amountToPay
                    else ReduceNoWarning);
              } in (case giveMoney accId payee token paidAmount newAccs of {
                     (payment, finalAccs) ->
                       let {
                         newState =
                           SemanticsTypes.accounts_update (\ _ -> finalAccs)
                             state;
                       } in Reduced warning payment newState cont;
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
        SemanticsTypes.Contract ->
          [ReduceWarning] -> [SemanticsTypes.Payment] -> ReduceResult;
reductionLoop reduced env state contract warnings payments =
  (case reduceContractStep env state contract of {
    Reduced warning effect newState cont ->
      let {
        newWarnings =
          (if equal_ReduceWarning warning ReduceNoWarning then warnings
            else warning : warnings);
        a = (case effect of {
              ReduceNoPayment -> payments;
              ReduceWithPayment payment -> payment : payments;
            });
      } in reductionLoop True env newState cont newWarnings a;
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

convertReduceWarnings :: [ReduceWarning] -> [SemanticsTypes.TransactionWarning];
convertReduceWarnings [] = [];
convertReduceWarnings (ReduceNoWarning : rest) = convertReduceWarnings rest;
convertReduceWarnings (ReduceNonPositivePay accId payee tok amount : rest) =
  SemanticsTypes.TransactionNonPositivePay accId payee tok amount :
    convertReduceWarnings rest;
convertReduceWarnings (ReducePartialPay accId payee tok paid expected : rest) =
  SemanticsTypes.TransactionPartialPay accId payee tok paid expected :
    convertReduceWarnings rest;
convertReduceWarnings (ReduceShadowing valId oldVal newVal : rest) =
  SemanticsTypes.TransactionShadowing valId oldVal newVal :
    convertReduceWarnings rest;
convertReduceWarnings (ReduceAssertionFailed : rest) =
  SemanticsTypes.TransactionAssertionFailed : convertReduceWarnings rest;

convertApplyWarning :: ApplyWarning -> [SemanticsTypes.TransactionWarning];
convertApplyWarning ApplyNoWarning = [];
convertApplyWarning (ApplyNonPositiveDeposit party accId tok amount) =
  [SemanticsTypes.TransactionNonPositiveDeposit party accId tok amount];

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
                 else ApplyNonPositiveDeposit party2 accId2 tok2 amount);
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
  (if SemanticsTypes.equal_ChoiceId choId1 choId2 &&
        SemanticsTypes.inBounds choice bounds
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
applyCases env state input [] = ApplyNoMatchError;

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
            [SemanticsTypes.TransactionWarning] ->
              [SemanticsTypes.Payment] -> ApplyAllResult;
applyAllLoop contractChanged env state contract inps warnings payments =
  (case reduceContractUntilQuiescent env state contract of {
    ContractQuiescent reduced reduceWarns pays curState cont ->
      (case inps of {
        [] -> ApplyAllSuccess (contractChanged || reduced)
                (warnings ++ convertReduceWarnings reduceWarns)
                (payments ++ pays) curState cont;
        input : rest ->
          (case applyInput env curState input cont of {
            Applied applyWarn newState appliedCont ->
              applyAllLoop True env newState appliedCont rest
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
applyAllInputs env state contract inps =
  applyAllLoop False env state contract inps [] [];

fixInterval ::
  (Arith.Int, Arith.Int) -> SemanticsTypes.State_ext () -> IntervalResult;
fixInterval (startTime, endTime) state =
  let {
    curMinTime = SemanticsTypes.minTime state;
    newMinTime = Orderings.max startTime curMinTime;
    env = SemanticsTypes.Environment_ext (newMinTime, endTime) ();
    newState = SemanticsTypes.minTime_update (\ _ -> newMinTime) state;
  } in (if Arith.less_int endTime startTime
         then IntervalError
                (SemanticsTypes.InvalidInterval (startTime, endTime))
         else (if Arith.less_int endTime curMinTime
                then IntervalError
                       (SemanticsTypes.IntervalInPastError curMinTime
                         (startTime, endTime))
                else IntervalTrimmed env newState));

computeTransaction ::
  SemanticsTypes.Transaction_ext () ->
    SemanticsTypes.State_ext () ->
      SemanticsTypes.Contract -> SemanticsTypes.TransactionOutput;
computeTransaction tx state contract =
  let {
    inps = SemanticsTypes.inputs tx;
  } in (case fixInterval (SemanticsTypes.interval tx) state of {
         IntervalTrimmed env fixSta ->
           (case applyAllInputs env fixSta contract inps of {
             ApplyAllSuccess reduced warnings payments newState cont ->
               (if not reduced &&
                     (not (SemanticsTypes.equal_Contract contract
                            SemanticsTypes.Close) ||
                       null (SemanticsTypes.accounts state))
                 then SemanticsTypes.TransactionError
                        SemanticsTypes.TEUselessTransaction
                 else SemanticsTypes.TransactionOutput
                        (SemanticsTypes.TransactionOutputRecord_ext warnings
                          payments newState cont ()));
             ApplyAllNoMatchError ->
               SemanticsTypes.TransactionError
                 SemanticsTypes.TEApplyNoMatchError;
             ApplyAllAmbiguousTimeIntervalError ->
               SemanticsTypes.TransactionError
                 SemanticsTypes.TEAmbiguousTimeIntervalError;
           });
         IntervalError errora ->
           SemanticsTypes.TransactionError
             (SemanticsTypes.TEIntervalError errora);
       });

playTraceAux ::
  SemanticsTypes.TransactionOutputRecord_ext () ->
    [SemanticsTypes.Transaction_ext ()] -> SemanticsTypes.TransactionOutput;
playTraceAux res [] = SemanticsTypes.TransactionOutput res;
playTraceAux
  (SemanticsTypes.TransactionOutputRecord_ext warnings payments state cont ())
  (h : t) =
  let {
    transRes = computeTransaction h state cont;
  } in (case transRes of {
         SemanticsTypes.TransactionOutput transResRec ->
           playTraceAux
             (SemanticsTypes.txOutWarnings_update
               (\ _ -> warnings ++ SemanticsTypes.txOutWarnings transResRec)
               (SemanticsTypes.txOutPayments_update
                 (\ _ -> payments ++ SemanticsTypes.txOutPayments transResRec)
                 transResRec))
             t;
         SemanticsTypes.TransactionError _ -> transRes;
       });

emptyState :: Arith.Int -> SemanticsTypes.State_ext ();
emptyState initialTime =
  SemanticsTypes.State_ext MList.empty MList.empty MList.empty initialTime ();

playTrace ::
  Arith.Int ->
    SemanticsTypes.Contract ->
      [SemanticsTypes.Transaction_ext ()] -> SemanticsTypes.TransactionOutput;
playTrace initialTime contract transactions =
  playTraceAux
    (SemanticsTypes.TransactionOutputRecord_ext [] [] (emptyState initialTime)
      contract ())
    transactions;

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
  (ReduceWithPayment
     (SemanticsTypes.Payment src (SemanticsTypes.Party p) tok m) :
    t)
  = (p, (tok, Arith.uminus_int m)) : getPartiesFromReduceEffect t;
getPartiesFromReduceEffect (ReduceNoPayment : t) = getPartiesFromReduceEffect t;
getPartiesFromReduceEffect
  (ReduceWithPayment
     (SemanticsTypes.Payment va (SemanticsTypes.Account ve) vc vd) :
    t)
  = getPartiesFromReduceEffect t;
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

isQuiescent :: SemanticsTypes.Contract -> SemanticsTypes.State_ext () -> Bool;
isQuiescent SemanticsTypes.Close state = null (SemanticsTypes.accounts state);
isQuiescent (SemanticsTypes.When uu uv uw) ux = True;
isQuiescent (SemanticsTypes.Pay v va vb vc vd) uz = False;
isQuiescent (SemanticsTypes.If v va vb) uz = False;
isQuiescent (SemanticsTypes.Let v va vb) uz = False;
isQuiescent (SemanticsTypes.Assert v va) uz = False;

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

equal_ReduceResult :: ReduceResult -> ReduceResult -> Bool;
equal_ReduceResult (ContractQuiescent x11 x12 x13 x14 x15)
  RRAmbiguousTimeIntervalError = False;
equal_ReduceResult RRAmbiguousTimeIntervalError
  (ContractQuiescent x11 x12 x13 x14 x15) = False;
equal_ReduceResult (ContractQuiescent x11 x12 x13 x14 x15)
  (ContractQuiescent y11 y12 y13 y14 y15) =
  x11 == y11 &&
    x12 == y12 &&
      x13 == y13 &&
        SemanticsTypes.equal_State_ext x14 y14 &&
          SemanticsTypes.equal_Contract x15 y15;
equal_ReduceResult RRAmbiguousTimeIntervalError RRAmbiguousTimeIntervalError =
  True;

}
