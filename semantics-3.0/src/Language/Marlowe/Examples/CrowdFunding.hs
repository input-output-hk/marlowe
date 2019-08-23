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

contract :: Contract
contract = crowdfunding 1000 10000 100 "1" ["2", "3", "4", "5"]

-- Limited crowdfunding example using embedding
crowdfunding :: Integer -> Integer -> Timeout -> Party -> [Party] -> Contract
crowdfunding target maxContrib tim p lp =
  multiState (transitionFunction maxContrib) [(cp, False) | cp <- lp] cont tim cont
  where cont = If (ValueGE (addAll srcAvail) (Constant target))
                  (payAllAccsTo srcAccs (Account creatorAcc) Refund)
                  Refund
        srcAccs = [AccountId 1 cp | cp <- lp]
        srcAvail = map AvailableMoney srcAccs
        creatorAcc = AccountId 1 p

-- Combines a list of Values using AddValue
addAll :: [Value] -> Value
addAll [] = (Constant 0)
addAll [a] = a
addAll l = AddValue (addAll b) (addAll a)
  where middle = (genericLength l) `div` (2 :: Integer)
        (b, a) = genericSplitAt middle l

-- Pay all money into an account to a payee
payAll :: AccountId -> Payee -> Contract -> Contract
payAll acId payee cont =
  Pay acId payee (AvailableMoney acId) cont

-- Pays all money available in a list of accounts to another account
payAllAccsTo :: [AccountId] -> Payee -> Contract -> Contract
payAllAccsTo [] _ c = c
payAllAccsTo (h:t) p c = payAll h p (payAllAccsTo t p c)

-- Defines a state machine for each contributor:
-- (party, False) - Has not chosen the amount to contribute
-- (party, True) - Has chosen the amount and is ready to make the deposit
type ContributionState = (Party, Bool)

transitionFunction :: Integer -> ContributionState -> (Maybe ContributionState, Action)
transitionFunction _ (party, True) =
  (Nothing,
   Deposit (AccountId 1 party) party (ChoiceValue (ChoiceId "1" party) (Constant 0)))
transitionFunction maxContrib (party, False) =
  (Just (party, True),
   Choice (ChoiceId "1" party) [Interval 0 maxContrib])

-- Interleaves a list of state machines defined by "f" transition function
-- and "l" list of initial states. If all state machines terminate continues
-- as "fc", if timeout "t" is reached before continue as "tc"
multiState :: (a -> (Maybe a, Action)) -> [a] -> Contract -> Timeout -> Contract
           -> Contract
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


