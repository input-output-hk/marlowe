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

data Party i = PubKey i
             | Role ByteString
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

type AccountId = Party
type ChoiceName = ByteString     -- Needs to be updated in playground.
type NumAccount = Integer
type Timeout = POSIXTime
type Money = Integer
type ChosenNum = Integer
type Accounts i t = Map (AccountId i, t) Integer

data ChoiceId i = ChoiceId ChoiceName (Party i)
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

data Value i t = AvailableMoney (Party i) t
               | Constant Integer
               | NegValue (Value i t)
               | AddValue (Value i t) (Value i t)
               | SubValue (Value i t) (Value i t)
               | MulValue (Value i t) (Value i t)
               | DivValue (Value i t) (Value i t)
               | ChoiceValue (ChoiceId i)
               | TimeIntervalStart
               | TimeIntervalEnd
               | UseValue ValueId
               | Cond (Observation i t) (Value i t) (Value i t)
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Observation i t = AndObs (Observation i t) (Observation i t)
                     | OrObs (Observation i t) (Observation i t)
                     | NotObs (Observation i t)
                     | ChoseSomething (ChoiceId i)
                     | ValueGE (Value i t) (Value i t)
                     | ValueGT (Value i t) (Value i t)
                     | ValueLT (Value i t) (Value i t)
                     | ValueLE (Value i t) (Value i t)
                     | ValueEQ (Value i t) (Value i t)
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

data Action i t = Deposit (Party i) (Party i) t (Value i t)
                | Choice (ChoiceId i) [Bound]
                | Notify (Observation i t)
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Payee i = Account (Party i)
             | Party (Party i)
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Case i t = Case (Action i t) (Contract i t)
              | MerkleizedCase (Action i t) ByteString
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

getAction :: Case i t -> Action i t
getAction (Case action _) = action
getAction (MerkleizedCase action _) = action

data Contract i t = Close
                  | Pay (Party i) (Payee i) t (Value i t) (Contract i t)
                  | If (Observation i t) (Contract i t) (Contract i t)
                  | When [Case i t] Timeout (Contract i t)
                  | Let ValueId (Value i t) (Contract i t)
                  | Assert (Observation i t) (Contract i t)
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data State i t = State { accounts    :: Map (Party i, t) Money
                       , choices     :: Map (ChoiceId i) ChosenNum
                       , boundValues :: Map ValueId Integer
                       , minTime     :: POSIXTime }
  deriving (Eq,Ord,Show,Read)

emptyState :: POSIXTime -> State i t
emptyState sn = State { accounts = Map.empty
                      , choices = Map.empty
                      , boundValues = Map.empty
                      , minTime = sn }

newtype Environment = Environment { timeInterval :: TimeInterval }
  deriving (Eq,Ord,Show,Read)

data InputContent i t = IDeposit (Party i) (Party i) t Money
                      | IChoice (ChoiceId i) ChosenNum
                      | INotify
  deriving (Eq,Ord,Show,Read)

data Input i t = NormalInput (InputContent i t)
               | MerkleizedInput (InputContent i t) ByteString
  deriving (Eq,Ord,Show,Read)

getInputContent :: Input i t -> InputContent i t
getInputContent (NormalInput inputContent) = inputContent
getInputContent (MerkleizedInput inputContent _) = inputContent

-- Processing of time interval
data IntervalError = InvalidInterval TimeInterval
                    | IntervalInPastError POSIXTime TimeInterval
  deriving (Eq,Ord,Show,Read)

data IntervalResult i t = IntervalTrimmed Environment (State i t)
                        | IntervalError IntervalError
  deriving (Eq,Ord,Show,Read)

