{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Marlowe.Examples.Auction where

import           Data.ByteString  (ByteString)
import           Data.Map.Strict  (Map)
import qualified Data.Map.Strict  as M
import           Data.String      (IsString (..) )
import           Language.Marlowe

main :: IO ()
main = print . pretty $ (contract ada "Alice" 100 1000 ["Bob", "Charlie", "Dora"] 10 :: Contract ByteString Token)

contract :: forall i t. Eq i => t -> Party i -> Integer -> Integer -> [String] -> POSIXTime -> Contract i t
contract tok owner minBid maxBid bidders deadline = go Nothing [] $ map fromString bidders
  where
    go :: Maybe (Value i t, Party i) -> [Party i] -> [Party i] -> Contract i t
    go m [] [] = settle m
    go m ps qs = When (map choose qs ++ map deposit ps) deadline $ settle m
      where
        --choose :: Party i -> Case
        choose p = Case (Choice (choice p) [Bound minBid maxBid]) $
            Let (value p) (ChoiceValue (choice p)) $
                go m (p : ps) $ filter (/= p) qs
        --deposit :: Party i -> Case
        deposit p =
            let v   = UseValue $ value p
                ps' = filter (/= p) ps
            in  Case (Deposit p p tok v) $ case m of
                    Nothing       -> go (Just (v, p)) ps' qs
                    Just (v', p') -> If (ValueGT v v')
                        (go (Just (v, p)) ps' qs)
                        (go m ps' qs)
    settle :: Maybe (Value i t, Party i) -> Contract i t
    settle Nothing       = Close
    settle (Just (v, p)) = Pay p (Party owner) tok v Close
    choice :: Party i -> ChoiceId i
    choice = ChoiceId "Bid"
    value :: Party i -> ValueId
    value p = head [fromString q | q <- bidders, fromString q == p]
