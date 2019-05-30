module Minimal where

type SlotNumber = Integer
type PubKey = Integer
type Party = PubKey
type NumChoice = Integer
type Timeout = SlotNumber 

data ChoiceId = ChoiceId NumChoice Party
  deriving (Eq,Ord,Show,Read)
data OracleId = OracleId PubKey
  deriving (Eq,Ord,Show,Read)

data Value = AvailableMoney |
             Constant Integer |
             CommittedBy Party |
             AddValue Value Value |
             SubValue Value Value |
             ChoiceValue ChoiceId Value |
             OracleValue OracleId Value |
             CurrentSlot
  deriving (Eq,Ord,Show,Read)

data Observation = AndObs Observation Observation |
                   OrObs Observation Observation |
                   NotObs Observation |
                   ChoseSomething ChoiceId |
                   OracleValueProvided OracleId |
                   ValueGE Value Value |
                   ValueGT Value Value |
                   ValueLT Value Value |
                   ValueLE Value Value |
                   ValueEQ Value Value |
                   TrueObs |
                   FalseObs
  deriving (Eq,Ord,Show,Read)

data Case = Case Observation Contract
  deriving (Eq,Ord,Show,Read)

data Contract =
    Pay [(Value, Party)] (Either Party Contract) |
    If Observation Contract Contract |
    When [Case] Timeout Contract
  deriving (Eq,Ord,Show,Read)

