{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Marlowe.Syntax.Translate where

import Language.Marlowe.Syntax.AbsMarlowe
import qualified Language.Marlowe.Semantics.Types as S
import           Data.ByteString (ByteString)
import           Data.ByteString.Char8 as BS (pack)
import           Data.Text as T (Text, pack)

class Translate a b where
  translate :: a -> b

instance Translate Value S.Value where
  translate (Constant c) = S.Constant c
  translate (AvailableMoney accId tok) = S.AvailableMoney (translate accId) (translate tok)
  translate (NegValue v) = S.NegValue $ translate v
  translate (AddValue lhs rhs) = S.AddValue (translate lhs) (translate rhs)
  translate (SubValue lhs rhs) = S.SubValue (translate lhs) (translate rhs)
  translate (MulValue lhs rhs) = S.MulValue (translate lhs) (translate rhs)
  translate (DivValue lhs rhs) = S.DivValue (translate lhs) (translate rhs)
  translate (ChoiceValue choId) = S.ChoiceValue (translate choId)
  translate TimeIntervalStart = S.TimeIntervalStart
  translate TimeIntervalEnd = S.TimeIntervalEnd
  translate (UseValue vId) = S.UseValue (translate vId)
  translate (Cond obs lhs rhs) = S.Cond (translate obs) (translate lhs) (translate rhs)

instance Translate Observation S.Observation where
  translate (AndObs lhs rhs) = S.AndObs (translate lhs) (translate rhs)
  translate (OrObs lhs rhs) = S.OrObs (translate lhs) (translate rhs)
  translate (NotObs v) = S.NotObs $ translate v
  translate (ChoseSomething choId) = S.ChoseSomething (translate choId)
  translate (ValueGE lhs rhs) = S.ValueGE (translate lhs) (translate rhs)
  translate (ValueGT lhs rhs) = S.ValueGT (translate lhs) (translate rhs)
  translate (ValueLT lhs rhs) = S.ValueLT (translate lhs) (translate rhs)
  translate (ValueLE lhs rhs) = S.ValueLE (translate lhs) (translate rhs)
  translate (ValueEQ lhs rhs) = S.ValueEQ (translate lhs) (translate rhs)
  translate TrueObs = S.TrueObs
  translate FalseObs = S.FalseObs

instance Translate Action S.Action where
  translate (Deposit accId party tok val) = S.Deposit (translate accId) (translate party) (translate tok) (translate val)
  translate (Choice choId bounds) = S.Choice (translate choId) (translate bounds)
  translate (Notify obs) = S.Notify $ translate obs

instance Translate Contract S.Contract where
  translate Close = S.Close
  translate (Pay accountId payee token value contract) = S.Pay (translate accountId) (translate payee) (translate token) (translate value) (translate contract)
  translate (If obs contract1 contract2) = S.If (translate obs) (translate contract1) (translate contract2)
  translate (When cases timeout contract) = S.When (translate <$> cases) (translate timeout) (translate contract)
  translate (Let valueId val contract) = S.Let (translate valueId) (translate val) (translate contract)
  translate (Assert obs contract) = S.Assert (translate obs) (translate contract)

instance Translate a b => Translate [a] [b] where
  translate = fmap translate

instance Translate String ByteString where
  translate = BS.pack

instance Translate String Text where
  translate = T.pack

instance Translate Case S.Case where
  translate (Case action contract) = S.Case (translate action) (translate contract)
  translate (MerkleizedCase action hash) = S.MerkleizedCase (translate action) (translate hash)

instance Translate Timeout S.Timeout where
  translate (Timeout i) = S.POSIXTime i

instance Translate Party S.Party where
  translate (Address address) = S.Address (translate address)
  translate (Role role) = S.Role (translate role)

instance Translate Bound S.Bound where
  translate (Bound i j) = S.Bound i j

instance Translate ValueId S.ValueId where
  translate (ValueId valueId) = S.ValueId (translate valueId)

instance Translate ChoiceId S.ChoiceId where
  translate (ChoiceId choiceId party) = S.ChoiceId (translate choiceId) (translate party)

instance Translate Token S.Token where
  translate (Token currencySymbol tokenName) = S.Token (translate currencySymbol) (translate tokenName)

type AccountId = Party

instance Translate Payee S.Payee where
  translate (Account accountId) = S.Account (translate accountId)
  translate (Party party) = S.Party (translate party)
