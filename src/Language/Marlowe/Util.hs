{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Marlowe.Util where
import           Data.List                        (foldl')
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.String                      (IsString(..))
import qualified Data.Text                        as T
import           Language.Marlowe.Semantics       (Payment(..))
import           Language.Marlowe.Semantics.Types (Input, InputContent(IDeposit), Payee(Party), ValueId(..),
                                                   Money, Party(..), getInputContent, Token (Token))
import           Data.Text.Encoding (encodeUtf8)

ada :: Token
ada = Token "" ""

instance IsString Party where
    fromString s = Role (encodeUtf8 $ T.pack s)

instance IsString ValueId where
    fromString s = ValueId (T.pack s)

aliceRole :: Party
aliceRole = Role "Alice"

aliceAcc :: Party
aliceAcc = aliceRole

bobRole :: Party
bobRole = Role "Bob"

bobAcc :: Party
bobAcc = bobRole

carolRole :: Party
carolRole = Role "Carol"

carolAcc :: Party
carolAcc = carolRole

charlieRole :: Party
charlieRole = Role "Charlie"

charlieAcc :: Party
charlieAcc = charlieRole

eveRole :: Party
eveRole = Role "Eve"

eveAcc :: Party
eveAcc = eveRole


type AccountsDiff = Map (Party, Token) Money


emptyAccountsDiff :: AccountsDiff
emptyAccountsDiff = Map.empty


isEmptyAccountsDiff :: AccountsDiff -> Bool
isEmptyAccountsDiff = all (== 0)


-- Adds a value to the map of outcomes
addAccountsDiff :: (Party, Token) -> Money -> AccountsDiff -> AccountsDiff
addAccountsDiff accId diffValue trOut = let
    newValue = case Map.lookup accId trOut of
        Just value -> value + diffValue
        Nothing    -> diffValue
    in Map.insert accId newValue trOut


-- | Extract total outcomes from transaction inputs and outputs
getAccountsDiff :: [Payment] -> [Input] -> AccountsDiff
getAccountsDiff payments inputs =
    foldl' (\acc (p, m) -> addAccountsDiff p m acc) emptyAccountsDiff (incomes ++ outcomes)
  where
    incomes  = [ ((p, t),  m) | IDeposit _ p t m <- map getInputContent inputs ]
    outcomes = [ ((p, t), -m) | Payment _ (Party p) t m  <- payments ]

