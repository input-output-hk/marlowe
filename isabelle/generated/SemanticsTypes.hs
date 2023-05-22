{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  SemanticsTypes(Party(..), equal_Party, ChoiceId(..), equal_ChoiceId,
                  ValueId(..), equal_ValueId, Token(..), equal_Token, Value(..),
                  Observation(..), equal_Observation, equal_Value, Payee(..),
                  equal_Payee, Bound(..), Action(..), Contract(..), Case(..),
                  equal_Action, equal_Contract, Input(..), equal_Input,
                  Payment(..), equal_Payment, TransactionWarning(..),
                  equal_TransactionWarning, IntervalError(..), State_ext(..),
                  TransactionError(..), TransactionOutputRecord_ext(..),
                  TransactionOutput(..), Environment_ext(..),
                  Transaction_ext(..), inBounds, choices, minTime, accounts,
                  boundValues, inputs, choices_update, minTime_update, interval,
                  accounts_update, timeInterval, boundValues_update, txOutState,
                  txOutContract, txOutPayments, txOutWarnings, equal_State_ext,
                  txOutPayments_update, txOutWarnings_update,
                  equal_IntervalError, equal_TransactionError,
                  equal_TransactionOutput, equal_Transaction_ext)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;

data Party = Address String | Role String deriving (Prelude.Read, Prelude.Show);

equal_Party :: Party -> Party -> Bool;
equal_Party (Address x1) (Role x2) = False;
equal_Party (Role x2) (Address x1) = False;
equal_Party (Role x2) (Role y2) = x2 == y2;
equal_Party (Address x1) (Address y1) = x1 == y1;

data ChoiceId = ChoiceId String Party deriving (Prelude.Read, Prelude.Show);

equal_ChoiceId :: ChoiceId -> ChoiceId -> Bool;
equal_ChoiceId (ChoiceId x1 x2) (ChoiceId y1 y2) =
  x1 == y1 && equal_Party x2 y2;

newtype ValueId = ValueId String deriving (Prelude.Read, Prelude.Show);

equal_ValueId :: ValueId -> ValueId -> Bool;
equal_ValueId (ValueId x) (ValueId ya) = x == ya;

data Token = Token String String deriving (Prelude.Read, Prelude.Show);

equal_Token :: Token -> Token -> Bool;
equal_Token (Token x1 x2) (Token y1 y2) = x1 == y1 && x2 == y2;

data Value = AvailableMoney Party Token | Constant Arith.Int | NegValue Value
  | AddValue Value Value | SubValue Value Value | MulValue Value Value
  | DivValue Value Value | ChoiceValue ChoiceId | TimeIntervalStart
  | TimeIntervalEnd | UseValue ValueId | Cond Observation Value Value
  deriving (Prelude.Read, Prelude.Show);

data Observation = AndObs Observation Observation
  | OrObs Observation Observation | NotObs Observation | ChoseSomething ChoiceId
  | ValueGE Value Value | ValueGT Value Value | ValueLT Value Value
  | ValueLE Value Value | ValueEQ Value Value | TrueObs | FalseObs
  deriving (Prelude.Read, Prelude.Show);

equal_Observation :: Observation -> Observation -> Bool;
equal_Observation TrueObs FalseObs = False;
equal_Observation FalseObs TrueObs = False;
equal_Observation (ValueEQ x91 x92) FalseObs = False;
equal_Observation FalseObs (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) TrueObs = False;
equal_Observation TrueObs (ValueEQ x91 x92) = False;
equal_Observation (ValueLE x81 x82) FalseObs = False;
equal_Observation FalseObs (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) TrueObs = False;
equal_Observation TrueObs (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (ValueLE x81 x82) = False;
equal_Observation (ValueLT x71 x72) FalseObs = False;
equal_Observation FalseObs (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) TrueObs = False;
equal_Observation TrueObs (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (ValueLT x71 x72) = False;
equal_Observation (ValueGT x61 x62) FalseObs = False;
equal_Observation FalseObs (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) TrueObs = False;
equal_Observation TrueObs (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (ValueGT x61 x62) = False;
equal_Observation (ValueGE x51 x52) FalseObs = False;
equal_Observation FalseObs (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) TrueObs = False;
equal_Observation TrueObs (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (ValueGE x51 x52) = False;
equal_Observation (ChoseSomething x4) FalseObs = False;
equal_Observation FalseObs (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) TrueObs = False;
equal_Observation TrueObs (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (ChoseSomething x4) = False;
equal_Observation (NotObs x3) FalseObs = False;
equal_Observation FalseObs (NotObs x3) = False;
equal_Observation (NotObs x3) TrueObs = False;
equal_Observation TrueObs (NotObs x3) = False;
equal_Observation (NotObs x3) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (NotObs x3) = False;
equal_Observation (NotObs x3) (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (NotObs x3) = False;
equal_Observation (NotObs x3) (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (NotObs x3) = False;
equal_Observation (NotObs x3) (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (NotObs x3) = False;
equal_Observation (NotObs x3) (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (NotObs x3) = False;
equal_Observation (NotObs x3) (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (NotObs x3) = False;
equal_Observation (OrObs x21 x22) FalseObs = False;
equal_Observation FalseObs (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) TrueObs = False;
equal_Observation TrueObs (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (NotObs x3) = False;
equal_Observation (NotObs x3) (OrObs x21 x22) = False;
equal_Observation (AndObs x11 x12) FalseObs = False;
equal_Observation FalseObs (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) TrueObs = False;
equal_Observation TrueObs (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (ValueEQ x91 x92) = False;
equal_Observation (ValueEQ x91 x92) (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (ValueLE x81 x82) = False;
equal_Observation (ValueLE x81 x82) (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (ValueLT x71 x72) = False;
equal_Observation (ValueLT x71 x72) (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (ValueGT x61 x62) = False;
equal_Observation (ValueGT x61 x62) (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (ValueGE x51 x52) = False;
equal_Observation (ValueGE x51 x52) (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (ChoseSomething x4) = False;
equal_Observation (ChoseSomething x4) (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (NotObs x3) = False;
equal_Observation (NotObs x3) (AndObs x11 x12) = False;
equal_Observation (AndObs x11 x12) (OrObs x21 x22) = False;
equal_Observation (OrObs x21 x22) (AndObs x11 x12) = False;
equal_Observation (ValueEQ x91 x92) (ValueEQ y91 y92) =
  equal_Value x91 y91 && equal_Value x92 y92;
equal_Observation (ValueLE x81 x82) (ValueLE y81 y82) =
  equal_Value x81 y81 && equal_Value x82 y82;
equal_Observation (ValueLT x71 x72) (ValueLT y71 y72) =
  equal_Value x71 y71 && equal_Value x72 y72;
equal_Observation (ValueGT x61 x62) (ValueGT y61 y62) =
  equal_Value x61 y61 && equal_Value x62 y62;
equal_Observation (ValueGE x51 x52) (ValueGE y51 y52) =
  equal_Value x51 y51 && equal_Value x52 y52;
equal_Observation (ChoseSomething x4) (ChoseSomething y4) =
  equal_ChoiceId x4 y4;
equal_Observation (NotObs x3) (NotObs y3) = equal_Observation x3 y3;
equal_Observation (OrObs x21 x22) (OrObs y21 y22) =
  equal_Observation x21 y21 && equal_Observation x22 y22;
equal_Observation (AndObs x11 x12) (AndObs y11 y12) =
  equal_Observation x11 y11 && equal_Observation x12 y12;
equal_Observation FalseObs FalseObs = True;
equal_Observation TrueObs TrueObs = True;

equal_Value :: Value -> Value -> Bool;
equal_Value (UseValue x11a) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (UseValue x11a) = False;
equal_Value TimeIntervalEnd (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (UseValue x11a) = False;
equal_Value (UseValue x11a) TimeIntervalEnd = False;
equal_Value TimeIntervalStart (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) TimeIntervalStart = False;
equal_Value TimeIntervalStart (UseValue x11a) = False;
equal_Value (UseValue x11a) TimeIntervalStart = False;
equal_Value TimeIntervalStart TimeIntervalEnd = False;
equal_Value TimeIntervalEnd TimeIntervalStart = False;
equal_Value (ChoiceValue x8) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (UseValue x11a) = False;
equal_Value (UseValue x11a) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) TimeIntervalStart = False;
equal_Value TimeIntervalStart (ChoiceValue x8) = False;
equal_Value (DivValue x71 x72) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (UseValue x11a) = False;
equal_Value (UseValue x11a) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) TimeIntervalStart = False;
equal_Value TimeIntervalStart (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (DivValue x71 x72) = False;
equal_Value (MulValue x61 x62) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (UseValue x11a) = False;
equal_Value (UseValue x11a) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) TimeIntervalStart = False;
equal_Value TimeIntervalStart (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (MulValue x61 x62) = False;
equal_Value (SubValue x51 x52) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (UseValue x11a) = False;
equal_Value (UseValue x11a) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) TimeIntervalStart = False;
equal_Value TimeIntervalStart (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (SubValue x51 x52) = False;
equal_Value (AddValue x41 x42) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (UseValue x11a) = False;
equal_Value (UseValue x11a) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) TimeIntervalStart = False;
equal_Value TimeIntervalStart (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (AddValue x41 x42) = False;
equal_Value (NegValue x3) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (NegValue x3) = False;
equal_Value (NegValue x3) (UseValue x11a) = False;
equal_Value (UseValue x11a) (NegValue x3) = False;
equal_Value (NegValue x3) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (NegValue x3) = False;
equal_Value (NegValue x3) TimeIntervalStart = False;
equal_Value TimeIntervalStart (NegValue x3) = False;
equal_Value (NegValue x3) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (NegValue x3) = False;
equal_Value (NegValue x3) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (NegValue x3) = False;
equal_Value (NegValue x3) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (NegValue x3) = False;
equal_Value (NegValue x3) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (NegValue x3) = False;
equal_Value (NegValue x3) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (NegValue x3) = False;
equal_Value (Constant x2) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (Constant x2) = False;
equal_Value (Constant x2) (UseValue x11a) = False;
equal_Value (UseValue x11a) (Constant x2) = False;
equal_Value (Constant x2) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (Constant x2) = False;
equal_Value (Constant x2) TimeIntervalStart = False;
equal_Value TimeIntervalStart (Constant x2) = False;
equal_Value (Constant x2) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (Constant x2) = False;
equal_Value (Constant x2) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (Constant x2) = False;
equal_Value (Constant x2) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (Constant x2) = False;
equal_Value (Constant x2) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (Constant x2) = False;
equal_Value (Constant x2) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (Constant x2) = False;
equal_Value (Constant x2) (NegValue x3) = False;
equal_Value (NegValue x3) (Constant x2) = False;
equal_Value (AvailableMoney x11 x12) (Cond x121 x122 x123) = False;
equal_Value (Cond x121 x122 x123) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (UseValue x11a) = False;
equal_Value (UseValue x11a) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) TimeIntervalEnd = False;
equal_Value TimeIntervalEnd (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) TimeIntervalStart = False;
equal_Value TimeIntervalStart (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (ChoiceValue x8) = False;
equal_Value (ChoiceValue x8) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (DivValue x71 x72) = False;
equal_Value (DivValue x71 x72) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (MulValue x61 x62) = False;
equal_Value (MulValue x61 x62) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (SubValue x51 x52) = False;
equal_Value (SubValue x51 x52) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (AddValue x41 x42) = False;
equal_Value (AddValue x41 x42) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (NegValue x3) = False;
equal_Value (NegValue x3) (AvailableMoney x11 x12) = False;
equal_Value (AvailableMoney x11 x12) (Constant x2) = False;
equal_Value (Constant x2) (AvailableMoney x11 x12) = False;
equal_Value (Cond x121 x122 x123) (Cond y121 y122 y123) =
  equal_Observation x121 y121 && equal_Value x122 y122 && equal_Value x123 y123;
equal_Value (UseValue x11a) (UseValue y11a) = equal_ValueId x11a y11a;
equal_Value (ChoiceValue x8) (ChoiceValue y8) = equal_ChoiceId x8 y8;
equal_Value (DivValue x71 x72) (DivValue y71 y72) =
  equal_Value x71 y71 && equal_Value x72 y72;
equal_Value (MulValue x61 x62) (MulValue y61 y62) =
  equal_Value x61 y61 && equal_Value x62 y62;
equal_Value (SubValue x51 x52) (SubValue y51 y52) =
  equal_Value x51 y51 && equal_Value x52 y52;
equal_Value (AddValue x41 x42) (AddValue y41 y42) =
  equal_Value x41 y41 && equal_Value x42 y42;
equal_Value (NegValue x3) (NegValue y3) = equal_Value x3 y3;
equal_Value (Constant x2) (Constant y2) = Arith.equal_int x2 y2;
equal_Value (AvailableMoney x11 x12) (AvailableMoney y11 y12) =
  equal_Party x11 y11 && equal_Token x12 y12;
equal_Value TimeIntervalEnd TimeIntervalEnd = True;
equal_Value TimeIntervalStart TimeIntervalStart = True;

data Payee = Account Party | Party Party deriving (Prelude.Read, Prelude.Show);

equal_Payee :: Payee -> Payee -> Bool;
equal_Payee (Account x1) (Party x2) = False;
equal_Payee (Party x2) (Account x1) = False;
equal_Payee (Party x2) (Party y2) = equal_Party x2 y2;
equal_Payee (Account x1) (Account y1) = equal_Party x1 y1;

data Bound = Bound Arith.Int Arith.Int deriving (Prelude.Read, Prelude.Show);

data Action = Deposit Party Party Token Value | Choice ChoiceId [Bound]
  | Notify Observation deriving (Prelude.Read, Prelude.Show);

data Contract = Close | Pay Party Payee Token Value Contract
  | If Observation Contract Contract | When [Case] Arith.Int Contract
  | Let ValueId Value Contract | Assert Observation Contract
  deriving (Prelude.Read, Prelude.Show);

data Case = Case Action Contract deriving (Prelude.Read, Prelude.Show);

equal_Bound :: Bound -> Bound -> Bool;
equal_Bound (Bound x1 x2) (Bound y1 y2) =
  Arith.equal_int x1 y1 && Arith.equal_int x2 y2;

instance Eq Bound where {
  a == b = equal_Bound a b;
};

equal_Action :: Action -> Action -> Bool;
equal_Action (Choice x21 x22) (Notify x3) = False;
equal_Action (Notify x3) (Choice x21 x22) = False;
equal_Action (Deposit x11 x12 x13 x14) (Notify x3) = False;
equal_Action (Notify x3) (Deposit x11 x12 x13 x14) = False;
equal_Action (Deposit x11 x12 x13 x14) (Choice x21 x22) = False;
equal_Action (Choice x21 x22) (Deposit x11 x12 x13 x14) = False;
equal_Action (Notify x3) (Notify y3) = equal_Observation x3 y3;
equal_Action (Choice x21 x22) (Choice y21 y22) =
  equal_ChoiceId x21 y21 && x22 == y22;
equal_Action (Deposit x11 x12 x13 x14) (Deposit y11 y12 y13 y14) =
  equal_Party x11 y11 &&
    equal_Party x12 y12 && equal_Token x13 y13 && equal_Value x14 y14;

instance Eq Case where {
  a == b = equal_Case a b;
};

equal_Contract :: Contract -> Contract -> Bool;
equal_Contract (Let x51 x52 x53) (Assert x61 x62) = False;
equal_Contract (Assert x61 x62) (Let x51 x52 x53) = False;
equal_Contract (When x41 x42 x43) (Assert x61 x62) = False;
equal_Contract (Assert x61 x62) (When x41 x42 x43) = False;
equal_Contract (When x41 x42 x43) (Let x51 x52 x53) = False;
equal_Contract (Let x51 x52 x53) (When x41 x42 x43) = False;
equal_Contract (If x31 x32 x33) (Assert x61 x62) = False;
equal_Contract (Assert x61 x62) (If x31 x32 x33) = False;
equal_Contract (If x31 x32 x33) (Let x51 x52 x53) = False;
equal_Contract (Let x51 x52 x53) (If x31 x32 x33) = False;
equal_Contract (If x31 x32 x33) (When x41 x42 x43) = False;
equal_Contract (When x41 x42 x43) (If x31 x32 x33) = False;
equal_Contract (Pay x21 x22 x23 x24 x25) (Assert x61 x62) = False;
equal_Contract (Assert x61 x62) (Pay x21 x22 x23 x24 x25) = False;
equal_Contract (Pay x21 x22 x23 x24 x25) (Let x51 x52 x53) = False;
equal_Contract (Let x51 x52 x53) (Pay x21 x22 x23 x24 x25) = False;
equal_Contract (Pay x21 x22 x23 x24 x25) (When x41 x42 x43) = False;
equal_Contract (When x41 x42 x43) (Pay x21 x22 x23 x24 x25) = False;
equal_Contract (Pay x21 x22 x23 x24 x25) (If x31 x32 x33) = False;
equal_Contract (If x31 x32 x33) (Pay x21 x22 x23 x24 x25) = False;
equal_Contract Close (Assert x61 x62) = False;
equal_Contract (Assert x61 x62) Close = False;
equal_Contract Close (Let x51 x52 x53) = False;
equal_Contract (Let x51 x52 x53) Close = False;
equal_Contract Close (When x41 x42 x43) = False;
equal_Contract (When x41 x42 x43) Close = False;
equal_Contract Close (If x31 x32 x33) = False;
equal_Contract (If x31 x32 x33) Close = False;
equal_Contract Close (Pay x21 x22 x23 x24 x25) = False;
equal_Contract (Pay x21 x22 x23 x24 x25) Close = False;
equal_Contract (Assert x61 x62) (Assert y61 y62) =
  equal_Observation x61 y61 && equal_Contract x62 y62;
equal_Contract (Let x51 x52 x53) (Let y51 y52 y53) =
  equal_ValueId x51 y51 && equal_Value x52 y52 && equal_Contract x53 y53;
equal_Contract (When x41 x42 x43) (When y41 y42 y43) =
  x41 == y41 && Arith.equal_int x42 y42 && equal_Contract x43 y43;
equal_Contract (If x31 x32 x33) (If y31 y32 y33) =
  equal_Observation x31 y31 && equal_Contract x32 y32 && equal_Contract x33 y33;
equal_Contract (Pay x21 x22 x23 x24 x25) (Pay y21 y22 y23 y24 y25) =
  equal_Party x21 y21 &&
    equal_Payee x22 y22 &&
      equal_Token x23 y23 && equal_Value x24 y24 && equal_Contract x25 y25;
equal_Contract Close Close = True;

equal_Case :: Case -> Case -> Bool;
equal_Case (Case x1 x2) (Case y1 y2) =
  equal_Action x1 y1 && equal_Contract x2 y2;

data Input = IDeposit Party Party Token Arith.Int | IChoice ChoiceId Arith.Int
  | INotify deriving (Prelude.Read, Prelude.Show);

equal_Input :: Input -> Input -> Bool;
equal_Input (IChoice x21 x22) INotify = False;
equal_Input INotify (IChoice x21 x22) = False;
equal_Input (IDeposit x11 x12 x13 x14) INotify = False;
equal_Input INotify (IDeposit x11 x12 x13 x14) = False;
equal_Input (IDeposit x11 x12 x13 x14) (IChoice x21 x22) = False;
equal_Input (IChoice x21 x22) (IDeposit x11 x12 x13 x14) = False;
equal_Input (IChoice x21 x22) (IChoice y21 y22) =
  equal_ChoiceId x21 y21 && Arith.equal_int x22 y22;
equal_Input (IDeposit x11 x12 x13 x14) (IDeposit y11 y12 y13 y14) =
  equal_Party x11 y11 &&
    equal_Party x12 y12 && equal_Token x13 y13 && Arith.equal_int x14 y14;
equal_Input INotify INotify = True;

instance Eq Input where {
  a == b = equal_Input a b;
};

instance Eq Party where {
  a == b = equal_Party a b;
};

instance Eq Token where {
  a == b = equal_Token a b;
};

data Payment = Payment Party Payee Token Arith.Int
  deriving (Prelude.Read, Prelude.Show);

equal_Payment :: Payment -> Payment -> Bool;
equal_Payment (Payment x1 x2 x3 x4) (Payment y1 y2 y3 y4) =
  equal_Party x1 y1 &&
    equal_Payee x2 y2 && equal_Token x3 y3 && Arith.equal_int x4 y4;

instance Eq Payment where {
  a == b = equal_Payment a b;
};

instance Eq ValueId where {
  a == b = equal_ValueId a b;
};

instance Eq ChoiceId where {
  a == b = equal_ChoiceId a b;
};

data TransactionWarning =
  TransactionNonPositiveDeposit Party Party Token Arith.Int
  | TransactionNonPositivePay Party Payee Token Arith.Int
  | TransactionPartialPay Party Payee Token Arith.Int Arith.Int
  | TransactionShadowing ValueId Arith.Int Arith.Int
  | TransactionAssertionFailed deriving (Prelude.Read, Prelude.Show);

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
  equal_ValueId x41 y41 && Arith.equal_int x42 y42 && Arith.equal_int x43 y43;
equal_TransactionWarning (TransactionPartialPay x31 x32 x33 x34 x35)
  (TransactionPartialPay y31 y32 y33 y34 y35) =
  equal_Party x31 y31 &&
    equal_Payee x32 y32 &&
      equal_Token x33 y33 && Arith.equal_int x34 y34 && Arith.equal_int x35 y35;
equal_TransactionWarning (TransactionNonPositivePay x21 x22 x23 x24)
  (TransactionNonPositivePay y21 y22 y23 y24) =
  equal_Party x21 y21 &&
    equal_Payee x22 y22 && equal_Token x23 y23 && Arith.equal_int x24 y24;
equal_TransactionWarning (TransactionNonPositiveDeposit x11 x12 x13 x14)
  (TransactionNonPositiveDeposit y11 y12 y13 y14) =
  equal_Party x11 y11 &&
    equal_Party x12 y12 && equal_Token x13 y13 && Arith.equal_int x14 y14;
equal_TransactionWarning TransactionAssertionFailed TransactionAssertionFailed =
  True;

instance Eq TransactionWarning where {
  a == b = equal_TransactionWarning a b;
};

data IntervalError = InvalidInterval (Arith.Int, Arith.Int)
  | IntervalInPastError Arith.Int (Arith.Int, Arith.Int)
  deriving (Prelude.Read, Prelude.Show);

data State_ext a =
  State_ext [((Party, Token), Arith.Int)] [(ChoiceId, Arith.Int)]
    [(ValueId, Arith.Int)] Arith.Int a
  deriving (Prelude.Read, Prelude.Show);

data TransactionError = TEAmbiguousTimeIntervalError | TEApplyNoMatchError
  | TEIntervalError IntervalError | TEUselessTransaction
  deriving (Prelude.Read, Prelude.Show);

data TransactionOutputRecord_ext a =
  TransactionOutputRecord_ext [TransactionWarning] [Payment] (State_ext ())
    Contract a
  deriving (Prelude.Read, Prelude.Show);

data TransactionOutput = TransactionOutput (TransactionOutputRecord_ext ())
  | TransactionError TransactionError deriving (Prelude.Read, Prelude.Show);

data Environment_ext a = Environment_ext (Arith.Int, Arith.Int) a
  deriving (Prelude.Read, Prelude.Show);

data Transaction_ext a = Transaction_ext (Arith.Int, Arith.Int) [Input] a
  deriving (Prelude.Read, Prelude.Show);

inBounds :: Arith.Int -> [Bound] -> Bool;
inBounds num =
  any (\ (Bound l u) -> Arith.less_eq_int l num && Arith.less_eq_int num u);

choices :: forall a. State_ext a -> [(ChoiceId, Arith.Int)];
choices (State_ext accounts choices boundValues minTime more) = choices;

minTime :: forall a. State_ext a -> Arith.Int;
minTime (State_ext accounts choices boundValues minTime more) = minTime;

accounts :: forall a. State_ext a -> [((Party, Token), Arith.Int)];
accounts (State_ext accounts choices boundValues minTime more) = accounts;

boundValues :: forall a. State_ext a -> [(ValueId, Arith.Int)];
boundValues (State_ext accounts choices boundValues minTime more) = boundValues;

inputs :: forall a. Transaction_ext a -> [Input];
inputs (Transaction_ext interval inputs more) = inputs;

choices_update ::
  forall a.
    ([(ChoiceId, Arith.Int)] -> [(ChoiceId, Arith.Int)]) ->
      State_ext a -> State_ext a;
choices_update choicesa (State_ext accounts choices boundValues minTime more) =
  State_ext accounts (choicesa choices) boundValues minTime more;

minTime_update ::
  forall a. (Arith.Int -> Arith.Int) -> State_ext a -> State_ext a;
minTime_update minTimea (State_ext accounts choices boundValues minTime more) =
  State_ext accounts choices boundValues (minTimea minTime) more;

interval :: forall a. Transaction_ext a -> (Arith.Int, Arith.Int);
interval (Transaction_ext interval inputs more) = interval;

accounts_update ::
  forall a.
    ([((Party, Token), Arith.Int)] -> [((Party, Token), Arith.Int)]) ->
      State_ext a -> State_ext a;
accounts_update accountsa (State_ext accounts choices boundValues minTime more)
  = State_ext (accountsa accounts) choices boundValues minTime more;

timeInterval :: forall a. Environment_ext a -> (Arith.Int, Arith.Int);
timeInterval (Environment_ext timeInterval more) = timeInterval;

boundValues_update ::
  forall a.
    ([(ValueId, Arith.Int)] -> [(ValueId, Arith.Int)]) ->
      State_ext a -> State_ext a;
boundValues_update boundValuesa
  (State_ext accounts choices boundValues minTime more) =
  State_ext accounts choices (boundValuesa boundValues) minTime more;

txOutState :: forall a. TransactionOutputRecord_ext a -> State_ext ();
txOutState
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutState;

txOutContract :: forall a. TransactionOutputRecord_ext a -> Contract;
txOutContract
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutContract;

txOutPayments :: forall a. TransactionOutputRecord_ext a -> [Payment];
txOutPayments
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutPayments;

txOutWarnings ::
  forall a. TransactionOutputRecord_ext a -> [TransactionWarning];
txOutWarnings
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutWarnings;

equal_State_ext :: forall a. (Eq a) => State_ext a -> State_ext a -> Bool;
equal_State_ext (State_ext accountsa choicesa boundValuesa minTimea morea)
  (State_ext accounts choices boundValues minTime more) =
  accountsa == accounts &&
    choicesa == choices &&
      boundValuesa == boundValues &&
        Arith.equal_int minTimea minTime && morea == more;

txOutPayments_update ::
  forall a.
    ([Payment] -> [Payment]) ->
      TransactionOutputRecord_ext a -> TransactionOutputRecord_ext a;
txOutPayments_update txOutPaymentsa
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = TransactionOutputRecord_ext txOutWarnings (txOutPaymentsa txOutPayments)
      txOutState txOutContract more;

txOutWarnings_update ::
  forall a.
    ([TransactionWarning] -> [TransactionWarning]) ->
      TransactionOutputRecord_ext a -> TransactionOutputRecord_ext a;
txOutWarnings_update txOutWarningsa
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = TransactionOutputRecord_ext (txOutWarningsa txOutWarnings) txOutPayments
      txOutState txOutContract more;

equal_IntervalError :: IntervalError -> IntervalError -> Bool;
equal_IntervalError (InvalidInterval x1) (IntervalInPastError x21 x22) = False;
equal_IntervalError (IntervalInPastError x21 x22) (InvalidInterval x1) = False;
equal_IntervalError (IntervalInPastError x21 x22) (IntervalInPastError y21 y22)
  = Arith.equal_int x21 y21 && x22 == y22;
equal_IntervalError (InvalidInterval x1) (InvalidInterval y1) = x1 == y1;

equal_TransactionError :: TransactionError -> TransactionError -> Bool;
equal_TransactionError (TEIntervalError x3) TEUselessTransaction = False;
equal_TransactionError TEUselessTransaction (TEIntervalError x3) = False;
equal_TransactionError TEApplyNoMatchError TEUselessTransaction = False;
equal_TransactionError TEUselessTransaction TEApplyNoMatchError = False;
equal_TransactionError TEApplyNoMatchError (TEIntervalError x3) = False;
equal_TransactionError (TEIntervalError x3) TEApplyNoMatchError = False;
equal_TransactionError TEAmbiguousTimeIntervalError TEUselessTransaction =
  False;
equal_TransactionError TEUselessTransaction TEAmbiguousTimeIntervalError =
  False;
equal_TransactionError TEAmbiguousTimeIntervalError (TEIntervalError x3) =
  False;
equal_TransactionError (TEIntervalError x3) TEAmbiguousTimeIntervalError =
  False;
equal_TransactionError TEAmbiguousTimeIntervalError TEApplyNoMatchError = False;
equal_TransactionError TEApplyNoMatchError TEAmbiguousTimeIntervalError = False;
equal_TransactionError (TEIntervalError x3) (TEIntervalError y3) =
  equal_IntervalError x3 y3;
equal_TransactionError TEUselessTransaction TEUselessTransaction = True;
equal_TransactionError TEApplyNoMatchError TEApplyNoMatchError = True;
equal_TransactionError TEAmbiguousTimeIntervalError TEAmbiguousTimeIntervalError
  = True;

equal_TransactionOutputRecord_ext ::
  forall a.
    (Eq a) => TransactionOutputRecord_ext a ->
                TransactionOutputRecord_ext a -> Bool;
equal_TransactionOutputRecord_ext
  (TransactionOutputRecord_ext txOutWarningsa txOutPaymentsa txOutStatea
    txOutContracta morea)
  (TransactionOutputRecord_ext txOutWarnings txOutPayments txOutState
    txOutContract more)
  = txOutWarningsa == txOutWarnings &&
      txOutPaymentsa == txOutPayments &&
        equal_State_ext txOutStatea txOutState &&
          equal_Contract txOutContracta txOutContract && morea == more;

equal_TransactionOutput :: TransactionOutput -> TransactionOutput -> Bool;
equal_TransactionOutput (TransactionOutput x1) (TransactionError x2) = False;
equal_TransactionOutput (TransactionError x2) (TransactionOutput x1) = False;
equal_TransactionOutput (TransactionError x2) (TransactionError y2) =
  equal_TransactionError x2 y2;
equal_TransactionOutput (TransactionOutput x1) (TransactionOutput y1) =
  equal_TransactionOutputRecord_ext x1 y1;

equal_Transaction_ext ::
  forall a. (Eq a) => Transaction_ext a -> Transaction_ext a -> Bool;
equal_Transaction_ext (Transaction_ext intervala inputsa morea)
  (Transaction_ext interval inputs more) =
  intervala == interval && inputsa == inputs && morea == more;

}
