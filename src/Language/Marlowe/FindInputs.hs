module Language.Marlowe.FindInputs(getAllInputs) where

import Language.Marlowe.SemanticsTypes (Contract(..), Case(..), Observation(..), Slot)
import Language.Marlowe.Analysis.FSSemanticsFastVerbose (warningsTrace)
import Language.Marlowe.Semantics (TransactionInput)
import Data.SBV (ThmResult)
import Data.Bifunctor (Bifunctor(second), bimap)
import Data.Maybe (catMaybes)

expandCase :: Case -> [Case]
expandCase (Case ac con) = [Case ac c | c <- expandContract con]
expandCase (MerkleizedCase _ _) = []

expandCases :: [Case] -> [[Case]]
expandCases [] = []
expandCases (firstCase:restOfCases) =
       [c:restOfCases | c <- expandCase firstCase]
    ++ [firstCase:ec | ec <- expandCases restOfCases]

expandContract :: Contract -> [Contract]
expandContract Close = [Assert FalseObs Close]
expandContract (Pay pa pa' to va con) = [Pay pa pa' to va c | c <- expandContract con]
expandContract (If ob con con') = [If ob c con' | c <- expandContract con]
                               ++ [If ob con c | c <- expandContract con']
expandContract (When cas sl con) = [When cas sl c | c <- expandContract con]
                                ++ [When c sl con | c <- expandCases cas]
expandContract (Let vi va con) = [Let vi va c | c <- expandContract con]
expandContract (Assert _ con) = expandContract con

getInputs :: Contract -> IO (Either (ThmResult, Contract) (Maybe (Slot, [TransactionInput])))
getInputs c = bimap (\tr -> (tr, c)) (fmap (\(s, t, _) -> (s, t))) <$> warningsTrace c

-- | Uses static analysis to obtain a list of "unit tests" (lists of transactions) that
-- | cover the different branches of the given contract. If static analysis fails
-- | it returns a tuple that includes the error by the solver and the offending
-- | extension of the contract
-- >>> import Language.Marlowe.Examples.EscrowSimple
-- >>> getAllInputs contract
-- Right [ (0, [ TransactionInput {txInterval = SlotInterval 10 10, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = SlotInterval 90 90, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "bob")) 0)]}
--             , TransactionInput {txInterval = SlotInterval 100 100, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "bob")) 0)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 0)]}
--             ])
--       , (0, [ TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "bob")) 0)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 1)]}
--             ])
--       , (0, [ TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "alice")) 0)]}
--             , TransactionInput {txInterval = SlotInterval 100 100, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "alice")) 0)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 0)]}
--             ])
--       , (0, [ TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "alice")) 0)]}
--             , TransactionInput {txInterval = SlotInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 1)]}
--             ])
--       ]
getAllInputs :: Contract -> IO (Either (ThmResult, Contract) [(Slot, [TransactionInput])])
getAllInputs c = second catMaybes . sequence <$> mapM getInputs (expandContract c)
