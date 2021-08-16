module Language.Marlowe.SemanticsSerialisation (contractToByteString) where

import           Data.Ratio (denominator, numerator)
import qualified Data.Text.Encoding as Text
import           Language.Marlowe.ExtendedBuilder (ExtendedBuilder)
import qualified Language.Marlowe.ExtendedBuilder as ExtendedBuilder
import           Language.Marlowe.SemanticsTypes (Action (..), Bound (Bound), Case (..), ChoiceId (..), Contract (..), Observation (..), Party (..), Payee (..), Slot (Slot), Token (..), Value (..), ValueId (..))
import           Language.Marlowe.Serialisation (intToByteString, listToByteString, packByteString, positiveIntToByteString)

partyToByteString :: Party -> ExtendedBuilder
partyToByteString (PubKey x) = positiveIntToByteString 0 <> packByteString (ExtendedBuilder.byteString x)
partyToByteString (Role x) = positiveIntToByteString 1 <> packByteString (ExtendedBuilder.byteString x)

choiceIdToByteString :: ChoiceId -> ExtendedBuilder
choiceIdToByteString (ChoiceId cn co) =
  packByteString (ExtendedBuilder.byteString cn) <> partyToByteString co

valueIdToByteString :: ValueId -> ExtendedBuilder
valueIdToByteString (ValueId n) = packByteString (ExtendedBuilder.byteString (Text.encodeUtf8 n))

tokenToByteString :: Token -> ExtendedBuilder
tokenToByteString (Token tn cs) = packByteString (ExtendedBuilder.byteString tn) <> packByteString (ExtendedBuilder.byteString cs)

observationToByteString :: Observation -> ExtendedBuilder
observationToByteString (NotObs subObs) = positiveIntToByteString 0 <> observationToByteString subObs
observationToByteString (AndObs lhs rhs) = positiveIntToByteString 1 <> observationToByteString lhs <> observationToByteString rhs
observationToByteString (OrObs lhs rhs) = positiveIntToByteString 2 <> observationToByteString lhs <> observationToByteString rhs
observationToByteString (ChoseSomething choId) = positiveIntToByteString 3 <> choiceIdToByteString choId
observationToByteString TrueObs = positiveIntToByteString 4
observationToByteString FalseObs = positiveIntToByteString 5
observationToByteString (ValueGE lhs rhs) = positiveIntToByteString 6 <> valueToByteString lhs <> valueToByteString rhs
observationToByteString (ValueGT lhs rhs) = positiveIntToByteString 7 <> valueToByteString lhs <> valueToByteString rhs
observationToByteString (ValueLT lhs rhs) = positiveIntToByteString 8 <> valueToByteString lhs <> valueToByteString rhs
observationToByteString (ValueLE lhs rhs) = positiveIntToByteString 9 <> valueToByteString lhs <> valueToByteString rhs
observationToByteString (ValueEQ lhs rhs) = positiveIntToByteString 10 <> valueToByteString lhs <> valueToByteString rhs

valueToByteString :: Value -> ExtendedBuilder
valueToByteString (AvailableMoney accId token) = positiveIntToByteString 0 <> partyToByteString accId <> tokenToByteString token
valueToByteString (Constant integer) = positiveIntToByteString 1 <> intToByteString integer
valueToByteString (NegValue val) = positiveIntToByteString 2 <> valueToByteString val
valueToByteString (AddValue lhs rhs) = positiveIntToByteString 3 <> valueToByteString lhs <> valueToByteString rhs
valueToByteString (SubValue lhs rhs) = positiveIntToByteString 4 <> valueToByteString lhs <> valueToByteString rhs
valueToByteString (MulValue lhs rhs) = positiveIntToByteString 5 <> valueToByteString lhs <> valueToByteString rhs
valueToByteString (Scale r rhs) = positiveIntToByteString 6 <> intToByteString (numerator r) <> intToByteString (denominator r) <> valueToByteString rhs
valueToByteString (ChoiceValue choId) = positiveIntToByteString 7 <> choiceIdToByteString choId
valueToByteString SlotIntervalStart = positiveIntToByteString 8
valueToByteString SlotIntervalEnd = positiveIntToByteString 9
valueToByteString (UseValue valId) = positiveIntToByteString 10 <> valueIdToByteString valId
valueToByteString (Cond cond thn els) = positiveIntToByteString 11 <> observationToByteString cond <> valueToByteString thn <> valueToByteString els

payeeToByteString :: Payee -> ExtendedBuilder
payeeToByteString (Account accId) = positiveIntToByteString 0 <> partyToByteString accId
payeeToByteString (Party party) = positiveIntToByteString 1 <> partyToByteString party

boundToByteString :: Bound -> ExtendedBuilder
boundToByteString (Bound l u) = intToByteString l <> intToByteString u

actionToByteString :: Action -> ExtendedBuilder
actionToByteString (Deposit accId party token val) = positiveIntToByteString 0 <> partyToByteString accId <> partyToByteString party <> tokenToByteString token <> valueToByteString val
actionToByteString (Choice choId bounds) = positiveIntToByteString 1 <> choiceIdToByteString choId <> listToByteString boundToByteString bounds
actionToByteString (Notify obs) = positiveIntToByteString 2 <> observationToByteString obs

caseToByteString :: Case -> ExtendedBuilder
caseToByteString (Case action cont) = positiveIntToByteString 0 <> actionToByteString action <> contractToByteString cont
caseToByteString (MerkleizedCase action bs) = positiveIntToByteString 1 <> actionToByteString action <> packByteString (ExtendedBuilder.byteString bs)

contractToByteString :: Contract -> ExtendedBuilder
contractToByteString Close = positiveIntToByteString 0
contractToByteString (Pay accId payee token val cont) = positiveIntToByteString 1 <> partyToByteString accId <> payeeToByteString payee <> tokenToByteString token <> valueToByteString val <> contractToByteString cont
contractToByteString (If obs cont1 cont2) = positiveIntToByteString 2 <> observationToByteString obs <> contractToByteString cont1 <> contractToByteString cont2
contractToByteString (When caseList (Slot timeout) cont) = positiveIntToByteString 3 <> listToByteString caseToByteString caseList <> intToByteString timeout <> contractToByteString cont
contractToByteString (Let valId val cont) = positiveIntToByteString 4 <> valueIdToByteString valId <> valueToByteString val <> contractToByteString cont
contractToByteString (Assert obs cont) = positiveIntToByteString 5 <> observationToByteString obs <> contractToByteString cont
