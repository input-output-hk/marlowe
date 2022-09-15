{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Marlowe.Semantics.Types where

import qualified Data.Text as T
import           GHC.Generics (Generic)
import           Data.Text (Text)
import           Language.Marlowe.Pretty (Pretty, prettyFragment)
import           Data.ByteString (ByteString)
import           Data.Bifoldable (Bifoldable (bifoldMap))
import           Data.Bifunctor (Bifunctor (bimap))
import           Data.Bitraversable (Bitraversable (bitraverse), bimapDefault, bifoldMapDefault)
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
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

type AccountId = Party
type ChoiceName = ByteString     -- Needs to be updated in playground.
type NumAccount = Integer
type Timeout = POSIXTime
type Money = Integer
type ChosenNum = Integer
type Accounts i t = Map (AccountId i, t) Integer

data ChoiceId i = ChoiceId ChoiceName (Party i)
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

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
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

instance Bifunctor  Value where bimap = bimapDefault
instance Bifoldable Value where bifoldMap = bifoldMapDefault
instance Bitraversable Value where
    bitraverse f g (AvailableMoney a b) = AvailableMoney <$> traverse f a <*> g b
    bitraverse _ _ (Constant x)         = pure (Constant x)
    bitraverse f g (NegValue a)         = NegValue <$> bitraverse f g a
    bitraverse f g (AddValue a b)       = AddValue <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (SubValue a b)       = SubValue <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (MulValue a b)       = MulValue <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (DivValue a b)       = DivValue <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f _ (ChoiceValue a)      = ChoiceValue <$> traverse f a
    bitraverse _ _ TimeIntervalStart    = pure TimeIntervalStart
    bitraverse _ _ TimeIntervalEnd      = pure TimeIntervalEnd
    bitraverse _ _ (UseValue a)         = pure (UseValue a)
    bitraverse f g (Cond a b c)         = Cond <$> bitraverse f g a <*> bitraverse f g b <*> bitraverse f g c

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
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

instance Bifunctor  Observation where bimap = bimapDefault
instance Bifoldable Observation where bifoldMap = bifoldMapDefault
instance Bitraversable Observation where
    bitraverse f g (AndObs a b)       = AndObs <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (OrObs a b)        = OrObs <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (NotObs a)         = NotObs <$> bitraverse f g a
    bitraverse f _ (ChoseSomething a) = ChoseSomething <$> traverse f a
    bitraverse f g (ValueGE a b)      = ValueGE <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (ValueGT a b)      = ValueGT <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (ValueLT a b)      = ValueLT <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (ValueLE a b)      = ValueLE <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (ValueEQ a b)      = ValueEQ <$> bitraverse f g a <*> bitraverse f g b
    bitraverse _ _ TrueObs            = pure TrueObs
    bitraverse _ _ FalseObs           = pure FalseObs

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
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

instance Bifunctor  Action where bimap = bimapDefault
instance Bifoldable Action where bifoldMap = bifoldMapDefault
instance Bitraversable Action where
    bitraverse f g (Deposit a b c d) = Deposit <$> traverse f a <*> traverse f b <*> g c <*> bitraverse f g d
    bitraverse f _ (Choice a b)      = Choice <$> traverse f a <*> pure b
    bitraverse f g (Notify a)        = Notify <$> bitraverse f g a

data Payee i = Account (Party i)
             | Party (Party i)
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

data Case i t = Case (Action i t) (Contract i t)
              | MerkleizedCase (Action i t) ByteString
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

instance Bifunctor  Case where bimap = bimapDefault
instance Bifoldable Case where bifoldMap = bifoldMapDefault
instance Bitraversable Case where
    bitraverse f g (Case   a b)         = Case <$> bitraverse f g a <*> bitraverse f g b
    bitraverse f g (MerkleizedCase a b) = MerkleizedCase <$> bitraverse f g a <*> pure b

getAction :: Case i t -> Action i t
getAction (Case action _) = action
getAction (MerkleizedCase action _) = action

data Contract i t = Close
                  | Pay (Party i) (Payee i) t (Value i t) (Contract i t)
                  | If (Observation i t) (Contract i t) (Contract i t)
                  | When [Case i t] Timeout (Contract i t)
                  | Let ValueId (Value i t) (Contract i t)
                  | Assert (Observation i t) (Contract i t)
  deriving (Eq,Ord,Show,Read,Generic,Pretty,Functor,Foldable,Traversable)

instance Bifunctor  Contract where bimap = bimapDefault
instance Bifoldable Contract where bifoldMap = bifoldMapDefault
instance Bitraversable Contract where
    bitraverse _ _ Close           = pure Close
    bitraverse f g (Pay a b c d e) = Pay <$> traverse f a <*> traverse f b <*> g c <*> bitraverse f g d <*> bitraverse f g e
    bitraverse f g (If a b c)      = If <$> bitraverse f g a <*> bitraverse f g b <*> bitraverse f g c
    bitraverse f g (When a b c)    = When <$> traverse (bitraverse f g) a <*> pure b <*> bitraverse f g c
    bitraverse f g (Let a b c)     = Let a <$> bitraverse f g b <*> bitraverse f g c
    bitraverse f g (Assert a b)    = Assert <$> bitraverse f g a <*> bitraverse f g b

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
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

instance Bifunctor  InputContent where bimap = bimapDefault
instance Bifoldable InputContent where bifoldMap = bifoldMapDefault
instance Bitraversable InputContent where
    bitraverse f g (IDeposit a b c d) = IDeposit <$> traverse f a <*> traverse f b <*> g c <*> pure d
    bitraverse f _ (IChoice a b)      = IChoice <$> traverse f a <*> pure b
    bitraverse _ _ INotify            = pure INotify

data Input i t = NormalInput (InputContent i t)
               | MerkleizedInput (InputContent i t) ByteString
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

instance Bifunctor  Input where bimap = bimapDefault
instance Bifoldable Input where bifoldMap = bifoldMapDefault
instance Bitraversable Input where
    bitraverse f g (NormalInput a)       = NormalInput <$> bitraverse f g a
    bitraverse f g (MerkleizedInput a b) = MerkleizedInput <$> bitraverse f g a <*> pure b

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

