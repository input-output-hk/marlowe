{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.CrowdFunding where

import           Language.Marlowe

import Data.List (genericLength, genericSplitAt, inits, tails)

splitEverywhere :: [a] -> [([a], a, [a])]
splitEverywhere xs =
   map
      (\(y, zs0) ->
         case zs0 of
            z:zs -> (y,z,zs)
            [] -> error "splitEverywhere: empty list")
      (init (zip (inits xs) (tails xs)))

contract :: t -> Contract i t
contract tok = crowdfunding tok 1000 10000 100 "1" ["2", "3", "4", "5"]

-- Limited crowdfunding example using embedding
crowdfunding :: t -> Integer -> Integer -> Timeout -> Party i -> [Party i] -> Contract i t
crowdfunding tok target maxContrib tim p lp =
  multiState (transitionFunction tok maxContrib) [(cp, False) | cp <- lp] cont tim cont
  where cont = If (ValueGE (addAll srcAvail) (Constant target))
                  (payAllAccsTo tok srcAccs (Account creatorAcc) Close)
                  Close
        srcAccs = lp
        srcAvail = map (`AvailableMoney` tok) srcAccs
        creatorAcc = p

-- Combines a list of Values using AddValue
addAll :: [Value i t] -> Value i t
addAll [] = Constant 0
addAll [a] = a
addAll l = AddValue (addAll b) (addAll a)
  where middle = genericLength l `div` (2 :: Integer)
        (b, a) = genericSplitAt middle l

-- Pay all money into an account to a payee
payAll :: t -> Party i -> Payee i -> Contract i t -> Contract i t
payAll tok acId payee cont =
  If (ValueGT (AvailableMoney acId tok) (Constant 0))
     (Pay acId payee tok (AvailableMoney acId tok) cont)
     cont

-- Pays all money available in a list of accounts to another account
payAllAccsTo :: t -> [Party i] -> Payee i -> Contract i t -> Contract i t
payAllAccsTo _   []    _ c = c
payAllAccsTo tok (h:t) p c = payAll tok h p (payAllAccsTo tok t p c)

-- Defines a state machine for each contributor:
-- (party, False) - Has not chosen the amount to contribute
-- (party, True) - Has chosen the amount and is ready to make the deposit
type ContributionState i = (Party i, Bool)

transitionFunction :: t -> Integer -> ContributionState i -> (Maybe (ContributionState i), Action i t)
transitionFunction tok _ (party, True) =
  (Nothing,
   Deposit party party tok (ChoiceValue (ChoiceId "1" party)))
transitionFunction tok maxContrib (party, False) =
  (Just (party, True),
   Choice (ChoiceId "1" party) [Bound 1 maxContrib])

-- Interleaves a list of state machines defined by "f" transition function
-- and "l" list of initial states. If all state machines terminate continues
-- as "fc", if timeout "t" is reached before continue as "tc"
multiState :: (a -> (Maybe a, Action i t)) -> [a] -> Contract i t -> Timeout -> Contract i t
           -> Contract i t
multiState _ [] fc _ _ = fc
multiState f l fc t tc =
  When [let (jna, ac) = f x in
        let nl = case jna of
                   Nothing -> b ++ a
                   Just na -> b ++ (na:a) in
        Case ac $ multiState f nl fc t tc
        | (b, x, a) <- splitEverywhere l]
       t
       tc


