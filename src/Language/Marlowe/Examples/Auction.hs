{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.Auction where

import           Data.Map.Strict  (Map)
import qualified Data.Map.Strict  as M
import           Data.String      (IsString (..) )
import           Language.Marlowe
main :: IO ()
main = print . pretty $ contract "Alice" 100 1000 ["Bob", "Charlie", "Dora"] 10
contract :: Party -> Integer -> Integer -> [String] -> Slot -> Contract
contract owner minBid maxBid bidders deadline = go Nothing [] $ map fromString bidders
  where
    go :: Maybe (Value, Party) -> [Party] -> [Party] -> Contract
    go m [] [] = settle m
    go m ps qs = When (map choose qs ++ map deposit ps) deadline $ settle m
      where
        --choose :: Party -> Case
        choose p = Case (Choice (choice p) [(Bound minBid maxBid)]) $
            Let (value p) (ChoiceValue (choice p)) $
                go m (p : ps) $ filter (/= p) qs
        --deposit :: Party -> Case
        deposit p =
            let v   = UseValue $ value p
                ps' = filter (/= p) ps
            in  Case (Deposit p p v) $ case m of
                    Nothing       -> go (Just (v, p)) ps' qs
                    Just (v', p') -> If (ValueGT v v')
                        (go (Just (v, p)) ps' qs)
                        (go m ps' qs)
    settle :: Maybe (Value, Party) -> Contract
    settle Nothing       = Close
    settle (Just (v, p)) = Pay p (Party owner) v Close
    choice :: Party -> ChoiceId
    choice = ChoiceId "Bid"
    value :: Party -> ValueId
    value p = head [fromString q | q <- bidders, fromString q == p]
