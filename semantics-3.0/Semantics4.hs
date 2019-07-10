module Semantics4 where

type SlotNumber = Integer
type PubKey = Integer
type Party = PubKey
type NumChoice = Integer
type NumAccount = Integer
type Timeout = SlotNumber

data AccountId = AccountId NumAccount Party
  deriving (Eq,Ord,Show,Read)
data ChoiceId = ChoiceId NumChoice Party
  deriving (Eq,Ord,Show,Read)
data OracleId = OracleId PubKey
  deriving (Eq,Ord,Show,Read)

data Value = AvailableMoney AccountId 
           | Constant Integer
           | NegValue Value
           | AddValue Value Value
           | SubValue Value Value
           | ChoiceValue ChoiceId Value
           | OracleValue OracleId Value
           | CurrentSlot
  deriving (Eq,Ord,Show,Read)

data Observation = AndObs Observation Observation
                 | OrObs Observation Observation
                 | NotObs Observation
                 | ChoseSomething ChoiceId
                 | OracleValueProvided OracleId
                 | ValueGE Value Value
                 | ValueGT Value Value
                 | ValueLT Value Value
                 | ValueLE Value Value
                 | ValueEQ Value Value
                 | TrueObs
                 | FalseObs
  deriving (Eq,Ord,Show,Read)

type Bound = (Integer, Integer)

data Action = Deposit AccountId Party Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving (Eq,Ord,Show,Read)

data Case = Case Action Contract
  deriving (Eq,Ord,Show,Read)

data Payee = Account AccountId
           | Party Party
  deriving (Eq,Ord,Show,Read)

data Contract = RefundAll
              | Pay AccountId Payee Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract
  deriving (Eq,Ord,Show,Read)

