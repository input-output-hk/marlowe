{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Marlowe.Semantics.Types where

import qualified Data.Text as T
import           GHC.Generics (Generic)
import           Data.Text (Text)
import           Language.Marlowe.Pretty (Pretty, prettyFragment)
import           Data.ByteString (ByteString)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Text.PrettyPrint.Leijen (text)

newtype POSIXTime = POSIXTime { getPOSIXTime :: Integer }
  deriving stock (Eq,Ord,Generic)
  deriving newtype (Pretty)

instance Show POSIXTime where
  showsPrec p (POSIXTime n) r = showsPrec p n r
instance Read POSIXTime where
  readsPrec p x = [(POSIXTime v, s) | (v, s) <- readsPrec p x]

instance Num POSIXTime where
    POSIXTime l + POSIXTime r = POSIXTime (l + r)
    POSIXTime l * POSIXTime r = POSIXTime (l * r)
    abs (POSIXTime l) = POSIXTime (abs l)
    signum (POSIXTime l) = POSIXTime (signum l)
    fromInteger = POSIXTime
    negate (POSIXTime l) = POSIXTime (negate l)

data Party = Address ByteString
           | Role ByteString
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

type AccountId = Party
type ChoiceName = ByteString     -- Needs to be updated in playground.
type NumAccount = Integer
type Timeout = POSIXTime
type Money = Integer
type ChosenNum = Integer
type Accounts = Map (AccountId, Token) Integer

data ChoiceId = ChoiceId ChoiceName Party
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

newtype ValueId = ValueId Text
  deriving stock (Eq,Ord,Generic)

data Token = Token ByteString ByteString
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

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
           | DivValue Value Value
           | ChoiceValue ChoiceId
           | TimeIntervalStart
           | TimeIntervalEnd
           | UseValue ValueId
           | Cond Observation Value Value
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

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
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data TimeInterval = TimeInterval POSIXTime POSIXTime
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

ivFrom, ivTo :: TimeInterval -> POSIXTime

ivFrom (TimeInterval from _) = from
ivTo   (TimeInterval _ to)   = to

data Bound = Bound Integer Integer
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = any (\(Bound l u) -> num >= l && num <= u)

data Action = Deposit Party Party Token Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Payee = Account Party
           | Party Party
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Case = Case Action Contract
          | MerkleizedCase Action ByteString
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

getAction :: Case -> Action
getAction (Case action _) = action
getAction (MerkleizedCase action _) = action

data Contract = Close
              | Pay Party Payee Token Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract
              | Let ValueId Value Contract
              | Assert Observation Contract
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data State = State { accounts    :: Map (Party, Token) Money
                   , choices     :: Map ChoiceId ChosenNum
                   , boundValues :: Map ValueId Integer
                   , minTime     :: POSIXTime }
  deriving (Eq,Ord,Show,Read)

emptyState :: POSIXTime -> State
emptyState sn = State { accounts = Map.empty
                      , choices = Map.empty
                      , boundValues = Map.empty
                      , minTime = sn }

newtype Environment = Environment { timeInterval :: TimeInterval }
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

-- Processing of time interval
data IntervalError = InvalidInterval TimeInterval
                    | IntervalInPastError POSIXTime TimeInterval
  deriving (Eq,Ord,Show,Read)

data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError IntervalError
  deriving (Eq,Ord,Show,Read)

