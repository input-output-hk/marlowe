module Escrow where

import           Semantics4

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
contract = When [Case (Deposit aliceAcc alice price)
                      (whenNOutOfMChoose
                         [ (refund, Refund)
                         , (pay, Pay aliceAcc (Party bob) price Refund)]
                         2
                         everybody
                         100
                         Refund)]
                10
                Refund

-- Continues as specified when N out of M have agreed on a choice,
-- continue as defCont if N can no longer agree, or on timeout

whenNOutOfMChoose :: [(ChosenNum, Contract)] -> Integer -> [Party] -> Integer -> Contract
                  -> Contract
whenNOutOfMChoose ops n m timeout defCont =
  whenNOutOfMChooseAux eops n m timeout defCont
  where eops = [(0, ch, co) | (ch, co) <- ops]

whenNOutOfMChooseAux :: [(Integer, ChosenNum, Contract)] -> Integer ->
                        [Party] -> Integer -> Contract
                     -> Contract
whenNOutOfMChooseAux [] _ _ _ defCont = defCont
whenNOutOfMChooseAux ops n partiesLeft timeout defCont
  | winnerVotes >= n = winnerCont
  | null cases = defCont
  | otherwise = When cases timeout defCont
  where
    (winnerVotes, _, winnerCont) = maximumBy (comparing (\(x, _, _) -> x)) ops
    votesLeft = genericLength partiesLeft
    cases = [ Case (Choice (ChoiceId 1 p) [(cchoice, cchoice)]) $
                   whenNOutOfMChooseAux (bo ++ (votes + 1, cchoice, cont) : bc)
                                        n (bp ++ ap) timeout defCont
             | (bp, p, ap) <- splitEverywhere partiesLeft
             , (bo, (votes, cchoice, cont), bc) <- splitEverywhere ops
             , votesLeft + votes >= n ]


-- Value under escrow
price :: Value
price = Constant 450

-- Alice's account
aliceAcc :: AccountId
aliceAcc = AccountId 1 alice

-- Participants

alice, bob, carol :: Party
alice = 1
bob = 2
carol = 3

everybody :: [Party]
everybody = [alice, bob, carol]

-- Possible votes
refund, pay :: ChosenNum
refund = 0
pay = 1

