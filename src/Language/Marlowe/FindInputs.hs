module Language.Marlowe.FindInputs (getAllInputs', getAllInputs) where

import Language.Marlowe.Semantics.Types (Contract(..), Case(..), Observation(..), POSIXTime, Token)
import Language.Marlowe.Semantics.Deserialisation (byteStringToContract)
import Language.Marlowe.Analysis.FSSemanticsFastVerbose (warningsTrace')
import Language.Marlowe.Semantics (TransactionInput)
import Data.ByteString (ByteString)
import Data.SBV (ThmResult)
import Data.Bifunctor (Bifunctor(second), bimap)
import Data.Maybe (catMaybes)


removeAsserts :: Contract i t -> Contract i t
removeAsserts = go
  where go :: Contract i t -> Contract i t
        go Close = Close
        go (Pay pa pa' to va con) = Pay pa pa' to va (go con)
        go (If ob con con') = If ob (go con) (go con')
        go (When cas sl con) = When (map goCase cas) sl (go con)
        go (Let vi va con) = Let vi va (go con)
        go (Assert _ con) = con

        goCase :: Case i t -> Case i t
        goCase (Case ac con) = Case ac (go con)
        goCase mc@(MerkleizedCase _ _) = mc

expandCase :: Case i t -> [Case i t]
expandCase (Case ac con) = [Case ac c | c <- expandContract con]
expandCase (MerkleizedCase _ _) = []

expandCases :: [Case i t] -> [[Case i t]]
expandCases [] = []
expandCases (firstCase:restOfCases) =
       [c:restOfCases | c <- expandCase firstCase]
    ++ [firstCase:ec | ec <- expandCases restOfCases]

expandContract :: Contract i t -> [Contract i t]
expandContract Close = [Assert FalseObs Close]
expandContract (Pay pa pa' to va con) = [Pay pa pa' to va c | c <- expandContract con]
expandContract (If ob con con') = [If ob c con' | c <- expandContract con]
                               ++ [If ob con c | c <- expandContract con']
expandContract (When cas sl con) = [When cas sl c | c <- expandContract con]
                                ++ [When c sl con | c <- expandCases cas]
expandContract (Let vi va con) = [Let vi va c | c <- expandContract con]
expandContract (Assert _ con) = expandContract con

getInputs :: (Ord i, Ord t) => (ByteString -> Maybe (Contract i t, ByteString)) -> Contract i t -> IO (Either (ThmResult, Contract i t) (Maybe (POSIXTime, [TransactionInput i t])))
getInputs decContract c = bimap (\tr -> (tr, c)) (fmap (\(s, t, _) -> (s, t))) <$> warningsTrace' decContract c

-- | Uses static analysis to obtain a list of "unit tests" (lists of transactions) that
-- | cover the different branches of the given contract. If static analysis fails
-- | it returns a tuple that includes the error by the solver and the offending
-- | extension of the contract
-- >>> import Language.Marlowe.Examples.EscrowSimple
-- >>> getAllInputs' contract
-- Right [ (0, [ TransactionInput {txInterval = TimeInterval 10 10, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = TimeInterval 90 90, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "bob")) 0)]}
--             , TransactionInput {txInterval = TimeInterval 100 100, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "bob")) 0)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 0)]}
--             ])
--       , (0, [ TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "bob")) 0)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 1)]}
--             ])
--       , (0, [ TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "alice")) 0)]}
--             , TransactionInput {txInterval = TimeInterval 100 100, txInputs = []}
--             ])
--       , (0, [ TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "alice")) 0)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 0)]}
--             ])
--       , (0, [ TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IDeposit (Role "alice") (Role "alice") (Token "" "") 450)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "claim" (Role "alice")) 0)]}
--             , TransactionInput {txInterval = TimeInterval 0 0, txInputs = [NormalInput (IChoice (ChoiceId "agree" (Role "carol")) 1)]}
--             ])
--       ]
getAllInputs' :: (Ord i, Ord t) => (ByteString -> Maybe (Contract i t, ByteString)) -> Contract i t -> IO (Either (ThmResult, Contract i t) [(POSIXTime, [TransactionInput i t])])
getAllInputs' decContract c = second catMaybes . sequence <$> mapM (getInputs decContract) (expandContract (removeAsserts c))

getAllInputs :: Contract ByteString Token -> IO (Either (ThmResult, Contract ByteString Token) [(POSIXTime, [TransactionInput ByteString Token])])
getAllInputs = getAllInputs' byteStringToContract
