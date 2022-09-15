{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Language.Marlowe.Examples.ExpCrowdFunding where

import           Language.Marlowe

contract :: Eq i => t -> Contract i t
contract tok = crowdfunding tok 1000 100

-- Limited crowdfunding example using embedding
crowdfunding :: Eq i => t -> Integer -> Timeout -> Contract i t
crowdfunding tok target tim =
  multiState tok [("2",False),("3",False),("4",False),("5",False)] cont tim cont
  where cont = If (ValueGE (AddValue (AddValue (AvailableMoney "2" tok)
                                               (AvailableMoney "3" tok))
                                     (AddValue (AvailableMoney "4" tok)
                                               (AvailableMoney "5" tok)))
                           (Constant target))
                  (Pay "2" (Account creatorAcc) tok (AvailableMoney "2" tok)
                       (Pay "3" (Account creatorAcc) tok (AvailableMoney "3" tok)
                            (Pay "4" (Account creatorAcc) tok (AvailableMoney "4" tok)
                                 (Pay "5" (Account creatorAcc) tok (AvailableMoney "5" tok)
                                      Close))))
                  Close
        creatorAcc = "1"

-- Defines a state machine for each contributor:
-- (party, False) - Has not chosen the amount to contribute
-- (party, True) - Has chosen the amount and is ready to make the deposit
type ContributionState i = (Party i, Bool)

multiState :: Eq i => t -> [ContributionState i] -> Contract i t -> Timeout -> Contract i t -> Contract i t
multiState tok [("2",False),("3",False),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("3",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("3",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("3",False),("4",False)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("3",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("3",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",True),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("3",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("3",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("3",False)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("3",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("3",False)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",False),("3",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",False),("5",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",False),("5",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("3",True),("4",False)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("3",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("3",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("3",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("3",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("3",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("3",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",False)] fc t tc)
       ] t tc
multiState tok [("2",False),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("4",False)] fc t tc)
       ] t tc
multiState tok [("2",False),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",False)] fc t tc)
       ] t tc
multiState tok [("2",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",False)] fc t tc)
       ] t tc
multiState tok [("2",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState tok [("2",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("3",False),("4",False)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("4",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("4",True),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("3",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("3",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("4",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("4",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("3",False)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("3",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("3",False)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("2",True),("3",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("4",False),("5",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("4",False),("5",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("3",True),("4",False)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("4",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("4",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("3",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("4",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("4",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("3",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("3",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("3",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("3",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("3",True)] fc t tc)
       , Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("2",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("4",False)] fc t tc)
       ] t tc
multiState tok [("2",True),("4",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("2",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("4",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("2",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("2",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("2",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("2",True)] fc t tc)
       ] t tc
multiState tok [("2",True)] fc t tc =
  When [ Case (Deposit "2" "2" tok (ChoiceValue (ChoiceId "1" "2"))) (multiState tok [] fc t tc)
       ] t tc
multiState tok [("3",False),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("3",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("3",False),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("3",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("3",False),("4",False)] fc t tc)
       ] t tc
multiState tok [("3",False),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("3",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("3",False),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("3",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("3",False),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("3",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("3",False),("4",True)] fc t tc)
       ] t tc
multiState tok [("3",False),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("3",False)] fc t tc)
       ] t tc
multiState tok [("3",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("3",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("3",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("3",False)] fc t tc)
       ] t tc
multiState tok [("3",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState tok [("3",True)] fc t tc)
       ] t tc
multiState tok [("3",True),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("3",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("3",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("3",True),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("3",True),("4",False)] fc t tc)
       ] t tc
multiState tok [("3",True),("4",False)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("3",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("3",True),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("3",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("3",True),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("3",True),("4",True)] fc t tc)
       ] t tc
multiState tok [("3",True),("4",True)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("4",True)] fc t tc)
       , Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("3",True)] fc t tc)
       ] t tc
multiState tok [("3",True),("5",False)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("3",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("3",True),("5",True)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("3",True)] fc t tc)
       ] t tc
multiState tok [("3",True)] fc t tc =
  When [ Case (Deposit "3" "3" tok (ChoiceValue (ChoiceId "1" "3"))) (multiState tok [] fc t tc)
       ] t tc
multiState tok [("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("4",False),("5",True)] fc t tc)
       ] t tc
multiState tok [("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("4",False)] fc t tc)
       ] t tc
multiState tok [("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState tok [("4",True)] fc t tc)
       ] t tc
multiState tok [("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("4",True),("5",True)] fc t tc)
       ] t tc
multiState tok [("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [("5",True)] fc t tc)
       , Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [("4",True)] fc t tc)
       ] t tc
multiState tok [("4",True)] fc t tc =
  When [ Case (Deposit "4" "4" tok (ChoiceValue (ChoiceId "1" "4"))) (multiState tok [] fc t tc)
       ] t tc
multiState tok [("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState tok [("5",True)] fc t tc)
       ] t tc
multiState tok [("5",True)] fc t tc =
  When [ Case (Deposit "5" "5" tok (ChoiceValue (ChoiceId "1" "5"))) (multiState tok [] fc t tc)
       ] t tc
multiState _toc [] fc t tc = fc

