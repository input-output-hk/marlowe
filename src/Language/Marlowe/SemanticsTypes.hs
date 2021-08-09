{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Marlowe.SemanticsTypes where

import qualified Data.Text as T
import           GHC.Generics (Generic)
import           Codec.Serialise (Serialise)
import           Data.Text (Text)
import           Language.Marlowe.Pretty (Pretty, prettyFragment)
import           Data.ByteString (ByteString)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Text.PrettyPrint.Leijen (text)

newtype Slot = Slot { getSlot :: Integer }
  deriving stock (Eq,Ord,Generic)
  deriving newtype (Pretty,Serialise)

instance Show Slot where
  showsPrec p (Slot n) r = showsPrec p n r
instance Read Slot where
  readsPrec p x = [(Slot v, s) | (v, s) <- readsPrec p x]

instance Num Slot where
    Slot l + Slot r = Slot (l + r)
    Slot l * Slot r = Slot (l * r)
    abs (Slot l) = Slot (abs l)
    signum (Slot l) = Slot (signum l)
    fromInteger = Slot
    negate (Slot l) = Slot (negate l)

data Party = PubKey ByteString
           | Role ByteString
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

type AccountId = Party
type ChoiceName = ByteString     -- Needs to be updated in playground.
type NumAccount = Integer
type Timeout = Slot
type Money = Integer
type ChosenNum = Integer
type Accounts = Map (AccountId, Token) Integer

data ChoiceId = ChoiceId ChoiceName Party
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

newtype ValueId = ValueId Text
  deriving stock (Eq,Ord,Generic)
  deriving anyclass Serialise

data Token = Token ByteString ByteString
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

instance Pretty ValueId where
  prettyFragment = text . show

instance Show ValueId where
  showsPrec p (ValueId txt) r = showsPrec p (T.unpack txt) r
instance Read ValueId where
  readsPrec p x = [(ValueId (T.pack v), s) | (v, s) <- readsPrec p x]

data Value = AvailableMoney Party Token
           | Constant Integer
           | NegValue Value
           | AddValue Value Value
           | SubValue Value Value
           | MulValue Value Value
           | Scale Rational Value
           | ChoiceValue ChoiceId
           | SlotIntervalStart
           | SlotIntervalEnd
           | UseValue ValueId
           | Cond Observation Value Value
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

data Observation = AndObs Observation Observation
                  | OrObs Observation Observation
                  | NotObs Observation
                  | ChoseSomething ChoiceId
                  | ValueGE Value Value
                  | ValueGT Value Value
                  | ValueLT Value Value
                  | ValueLE Value Value
                  | ValueEQ Value Value
                  | TrueObs
                  | FalseObs
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

data SlotInterval = SlotInterval Slot Slot
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

ivFrom, ivTo :: SlotInterval -> Slot

ivFrom (SlotInterval from _) = from
ivTo   (SlotInterval _ to)   = to

data Bound = Bound Integer Integer
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = any (\(Bound l u) -> num >= l && num <= u)

data Action = Deposit Party Party Token Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

data Payee = Account Party
           | Party Party
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

data Case = Case Action Contract
          | MerkleizedCase Action ByteString
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

getAction :: Case -> Action
getAction (Case action _) = action
getAction (MerkleizedCase action _) = action

data Contract = Close
              | Pay Party Payee Token Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract
              | Let ValueId Value Contract
              | Assert Observation Contract
  deriving (Eq,Ord,Show,Read,Generic,Serialise,Pretty)

data State = State { accounts    :: Map (Party, Token) Money
                   , choices     :: Map ChoiceId ChosenNum
                   , boundValues :: Map ValueId Integer
                   , minSlot     :: Slot }
  deriving (Eq,Ord,Show,Read)

emptyState :: Slot -> State
emptyState sn = State { accounts = Map.empty
                      , choices = Map.empty
                      , boundValues = Map.empty
                      , minSlot = sn }

newtype Environment = Environment { slotInterval :: SlotInterval }
  deriving (Eq,Ord,Show,Read)

data InputContent = IDeposit Party Party Token Money
                  | IChoice ChoiceId ChosenNum
                  | INotify
  deriving (Eq,Ord,Show,Read)

data Input = NormalInput InputContent
           | MerkleizedInput InputContent ByteString
  deriving (Eq,Ord,Show,Read)

getInputContent :: Input -> InputContent
getInputContent (NormalInput inputContent) = inputContent
getInputContent (MerkleizedInput inputContent _) = inputContent

-- Processing of slot interval
data IntervalError = InvalidInterval SlotInterval
                    | IntervalInPastError Slot SlotInterval
  deriving (Eq,Ord,Show,Read)

data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError IntervalError
  deriving (Eq,Ord,Show,Read)

