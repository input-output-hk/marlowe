{-# LANGUAGE OverloadedStrings #-}

-- This module has some missing Eq instances that werent exported by isabelle
-- directly. Ideally we should fix this from the Isabelle CodeExports.thy
-- theory.
module CoreOrphanEq where

import SemanticsTypes (Action, Contract, Payee, Value, Observation, State_ext, IntervalError, equal_Contract, equal_Payee, equal_Value, equal_Observation, equal_Action, equal_State_ext, equal_IntervalError)
import Semantics (Transaction_ext, TransactionError, TransactionOutput, equal_Transaction_ext, equal_TransactionError, equal_TransactionOutput)

instance Eq Contract where {
  a == b = equal_Contract a b;
};

instance Eq Payee where {
  a == b = equal_Payee a b;
}


instance Eq Value where {
  a == b = equal_Value a b;
};


instance Eq Observation where {
  a == b = equal_Observation a b;
};


instance Eq Action where {
  a == b = equal_Action a b;
};


instance Eq a => Eq (Transaction_ext a) where {
  a == b = equal_Transaction_ext a b;
};

instance Eq a => Eq (State_ext a) where {
  a == b = equal_State_ext a b;
};

instance Eq IntervalError where {
  a == b = equal_IntervalError a b;
};

instance Eq TransactionError where {
  a == b = equal_TransactionError a b;
};

instance Eq TransactionOutput where {
  a == b = equal_TransactionOutput a b;
}

