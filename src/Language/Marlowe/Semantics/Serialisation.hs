{-# OPTIONS_GHC -Wall #-}

module Language.Marlowe.Semantics.Serialisation (contractToByteString', contractToByteString) where

import           Data.ByteString (ByteString)
import qualified Data.Text.Encoding as Text
import           Language.Marlowe.ExtendedBuilder (ExtendedBuilder)
import qualified Language.Marlowe.ExtendedBuilder as ExtendedBuilder
import           Language.Marlowe.Semantics.Types (Action (..), Bound (Bound), Case (..), ChoiceId (..), Contract (..), Observation (..), Party (..), Payee (..), POSIXTime (POSIXTime), Token (..), Value (..), ValueId (..))
import           Language.Marlowe.Serialisation (intToByteString, listToByteString, packByteString, positiveIntToByteString)

partyToByteString :: (i -> ExtendedBuilder) -> Party i -> ExtendedBuilder
partyToByteString encI (PubKey x) = positiveIntToByteString 0 <> packByteString (encI x)
partyToByteString _ (Role x) = positiveIntToByteString 1 <> packByteString (ExtendedBuilder.byteString x)

choiceIdToByteString :: (i -> ExtendedBuilder) -> ChoiceId i -> ExtendedBuilder
choiceIdToByteString encI (ChoiceId cn co) =
  packByteString (ExtendedBuilder.byteString cn) <> partyToByteString encI co

valueIdToByteString :: ValueId -> ExtendedBuilder
valueIdToByteString (ValueId n) = packByteString (ExtendedBuilder.byteString (Text.encodeUtf8 n))

tokenToByteString :: Token -> ExtendedBuilder
tokenToByteString (Token cs tn) = packByteString (ExtendedBuilder.byteString cs) <> packByteString (ExtendedBuilder.byteString tn)

observationToByteString :: (i -> ExtendedBuilder) -> (t -> ExtendedBuilder) -> Observation i t -> ExtendedBuilder
observationToByteString  encI  encT (NotObs subObs) = positiveIntToByteString 0 <> observationToByteString encI encT subObs
observationToByteString  encI  encT (AndObs lhs rhs) = positiveIntToByteString 1 <> observationToByteString encI encT lhs <> observationToByteString encI encT rhs
observationToByteString  encI  encT (OrObs lhs rhs) = positiveIntToByteString 2 <> observationToByteString encI encT lhs <> observationToByteString encI encT rhs
observationToByteString  encI _encT (ChoseSomething choId) = positiveIntToByteString 3 <> choiceIdToByteString encI choId
observationToByteString _encI _encT TrueObs = positiveIntToByteString 4
observationToByteString _encI _encT FalseObs = positiveIntToByteString 5
observationToByteString  encI  encT (ValueGE lhs rhs) = positiveIntToByteString 6 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
observationToByteString  encI  encT (ValueGT lhs rhs) = positiveIntToByteString 7 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
observationToByteString  encI  encT (ValueLT lhs rhs) = positiveIntToByteString 8 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
observationToByteString  encI  encT (ValueLE lhs rhs) = positiveIntToByteString 9 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
observationToByteString  encI  encT (ValueEQ lhs rhs) = positiveIntToByteString 10 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs

valueToByteString :: (i -> ExtendedBuilder) -> (t -> ExtendedBuilder) -> Value i t -> ExtendedBuilder
valueToByteString  encI  encT (AvailableMoney accId token) = positiveIntToByteString 0 <> partyToByteString encI accId <> encT token
valueToByteString _encI _encT (Constant integer) = positiveIntToByteString 1 <> intToByteString integer
valueToByteString  encI  encT (NegValue val) = positiveIntToByteString 2 <> valueToByteString encI encT val
valueToByteString  encI  encT (AddValue lhs rhs) = positiveIntToByteString 3 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
valueToByteString  encI  encT (SubValue lhs rhs) = positiveIntToByteString 4 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
valueToByteString  encI  encT (MulValue lhs rhs) = positiveIntToByteString 5 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
valueToByteString  encI  encT (DivValue lhs rhs) = positiveIntToByteString 6 <> valueToByteString encI encT lhs <> valueToByteString encI encT rhs
valueToByteString  encI _encT (ChoiceValue choId) = positiveIntToByteString 7 <> choiceIdToByteString  encI choId
valueToByteString _encI _encT TimeIntervalStart = positiveIntToByteString 8
valueToByteString _encI _encT TimeIntervalEnd = positiveIntToByteString 9
valueToByteString _encI _encT (UseValue valId) = positiveIntToByteString 10 <> valueIdToByteString valId
valueToByteString  encI  encT (Cond cond thn els) = positiveIntToByteString 11 <> observationToByteString encI encT cond <> valueToByteString encI encT thn <> valueToByteString encI encT els

payeeToByteString :: (i -> ExtendedBuilder) -> Payee i-> ExtendedBuilder
payeeToByteString encI (Account accId) = positiveIntToByteString 0 <> partyToByteString encI accId
payeeToByteString encI (Party party) = positiveIntToByteString 1 <> partyToByteString encI party

boundToByteString :: Bound -> ExtendedBuilder
boundToByteString (Bound l u) = intToByteString l <> intToByteString u

actionToByteString :: (i -> ExtendedBuilder) -> (t -> ExtendedBuilder) -> Action i t -> ExtendedBuilder
actionToByteString encI  encT (Deposit accId party token val) = positiveIntToByteString 0 <> partyToByteString encI accId <> partyToByteString encI party <> encT token <> valueToByteString encI encT val
actionToByteString encI _encT (Choice choId bounds) = positiveIntToByteString 1 <> choiceIdToByteString encI choId <> listToByteString boundToByteString bounds
actionToByteString encI  encT (Notify obs) = positiveIntToByteString 2 <> observationToByteString encI encT obs

caseToByteString :: (i -> ExtendedBuilder) -> (t -> ExtendedBuilder) -> Case i t -> ExtendedBuilder
caseToByteString encI encT (Case action cont) = positiveIntToByteString 0 <> actionToByteString encI encT action <> contractToByteString' encI encT cont
caseToByteString encI encT (MerkleizedCase action bs) = positiveIntToByteString 1 <> actionToByteString encI encT action <> packByteString (ExtendedBuilder.byteString bs)

contractToByteString' :: (i -> ExtendedBuilder) -> (t -> ExtendedBuilder) -> Contract i t -> ExtendedBuilder
contractToByteString' _encI _encT Close = positiveIntToByteString 0
contractToByteString'  encI  encT (Pay accId payee token val cont) = positiveIntToByteString 1 <> partyToByteString encI accId <> payeeToByteString encI payee <> encT token <> valueToByteString encI encT val <> contractToByteString' encI encT cont
contractToByteString'  encI  encT (If obs cont1 cont2) = positiveIntToByteString 2 <> observationToByteString encI encT obs <> contractToByteString' encI encT cont1 <> contractToByteString' encI encT cont2
contractToByteString'  encI  encT (When caseList (POSIXTime timeout) cont) = positiveIntToByteString 3 <> listToByteString (caseToByteString encI encT) caseList <> intToByteString timeout <> contractToByteString' encI encT cont
contractToByteString'  encI  encT (Let valId val cont) = positiveIntToByteString 4 <> valueIdToByteString valId <> valueToByteString encI encT val <> contractToByteString' encI encT cont
contractToByteString'  encI  encT (Assert obs cont) = positiveIntToByteString 5 <> observationToByteString encI encT obs <> contractToByteString' encI encT cont

contractToByteString :: Contract ByteString Token -> ExtendedBuilder
contractToByteString = contractToByteString' ExtendedBuilder.byteString tokenToByteString
