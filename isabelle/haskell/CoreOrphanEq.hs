{-# LANGUAGE OverloadedStrings #-}

-- This module has some missing Eq instances that werent exported by isabelle
-- directly. Ideally we should fix this from the Isabelle CodeExports.thy
-- theory.
module CoreOrphanEq where

import SemanticsTypes (Action, Contract, Payee, Value, Observation, equal_Contract, equal_Payee, equal_Value, equal_Observation, equal_Action)
import Semantics (TransactionWarning, Payment, equal_TransactionWarning, equal_Payment)

instance Eq Contract where {
  a == b = equal_Contract a b;
};

instance Eq TransactionWarning where {
  a == b = equal_TransactionWarning a b;
}

instance Eq Payment where {
  a == b = equal_Payment a b;
}

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