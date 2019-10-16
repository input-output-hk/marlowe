{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.Escrow where

import           Language.Marlowe

import Data.List (maximumBy, genericLength, inits, tails)
import Data.Ord (comparing)

splitEverywhere :: [a] -> [([a], a, [a])]
splitEverywhere xs =
   map
      (\(y, zs0) ->
         case zs0 of
            z:zs -> (y,z,zs)
            [] -> error "splitEverywhere: empty list")
      (init (zip (inits xs) (tails xs)))

-- Escrow example using embedding

contract :: Contract
contract = When [Case (Deposit aliceAcc alicePubKey price)
                      (whenNOutOfMChoose
                         [ (refund, Close)
                         , (pay, Pay aliceAcc (Party bobPubKey) price Close)]
                         2
                         everybody
                         100
                         Close)]
                10
                Close

-- Continues as specified when N out of M have agreed on a choice,
-- continue as defCont if N can no longer agree, or on timeout

whenNOutOfMChoose :: [(ChosenNum, Contract)] -> Integer -> [Party] -> Slot -> Contract
                  -> Contract
whenNOutOfMChoose ops n m timeout defCont =
  whenNOutOfMChooseAux eops n m timeout defCont
  where eops = [(0, ch, co) | (ch, co) <- ops]

whenNOutOfMChooseAux :: [(Integer, ChosenNum, Contract)] -> Integer ->
                        [Party] -> Slot -> Contract
                     -> Contract
whenNOutOfMChooseAux [] _ _ _ defCont = defCont
whenNOutOfMChooseAux ops n partiesLeft timeout defCont
  | winnerVotes >= n = winnerCont
  | null cases = defCont
  | otherwise = When cases timeout defCont
  where
    (winnerVotes, _, winnerCont) = maximumBy (comparing (\(x, _, _) -> x)) ops
    votesLeft = genericLength partiesLeft
    cases = [ Case (Choice (ChoiceId "OK" p) [Bound cchoice cchoice]) $
                   whenNOutOfMChooseAux (bo ++ (votes + 1, cchoice, cont) : bc)
                                        n (bp ++ ap) timeout defCont
             | (bp, p, ap) <- splitEverywhere partiesLeft
             , (bo, (votes, cchoice, cont), bc) <- splitEverywhere ops
             , votesLeft + votes >= n ]


-- Value under escrow
price :: Value
price = Constant 450

-- Participants

everybody :: [Party]
everybody = [alicePubKey, bobPubKey, carolPubKey]

-- Possible votes
refund, pay :: ChosenNum
refund = 0
pay = 1

