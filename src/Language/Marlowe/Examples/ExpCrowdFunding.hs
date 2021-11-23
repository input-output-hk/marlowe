{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.ExpCrowdFunding where

import           Language.Marlowe

contract :: Contract
contract = crowdfunding 1000 100

-- Limited crowdfunding example using embedding
crowdfunding :: Integer -> Timeout -> Contract
crowdfunding target tim =
  multiState [("2",False),("3",False),("4",False),("5",False)] cont tim cont
  where cont = If (ValueGE (AddValue (AddValue (AvailableMoney "2" ada)
                                               (AvailableMoney "3" ada))
                                     (AddValue (AvailableMoney "4" ada)
                                               (AvailableMoney "5" ada)))
                           (Constant target))
                  (Pay "2" (Account creatorAcc) ada (AvailableMoney "2" ada)
                       (Pay "3" (Account creatorAcc) ada (AvailableMoney "3" ada)
                            (Pay "4" (Account creatorAcc) ada (AvailableMoney "4" ada)
                                 (Pay "5" (Account creatorAcc) ada (AvailableMoney "5" ada)
                                      Close))))
                  Close
        creatorAcc = "1"

-- Defines a state machine for each contributor:
-- (party, False) - Has not chosen the amount to contribute
-- (party, True) - Has chosen the amount and is ready to make the deposit
type ContributionState = (Party, Bool)

multiState :: [ContributionState] -> Contract -> Timeout -> Contract -> Contract
multiState [("2",False),("3",False),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("3",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",False),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("3",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("3",False),("4",False)] fc t tc)
       ] t tc
multiState [("2",False),("3",False),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("3",False),("4",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",False),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("3",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",False),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",True),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("3",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("3",False),("4",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",False),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("3",False)] fc t tc)
       ] t tc
multiState [("2",False),("3",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("3",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("3",False)] fc t tc)
       ] t tc
multiState [("2",False),("3",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",False),("3",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",False),("5",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",False),("5",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("3",True),("4",False)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("3",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("3",True),("4",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("3",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("3",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("3",True)] fc t tc)
       ] t tc
multiState [("2",False),("3",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("3",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",False)] fc t tc)
       ] t tc
multiState [("2",False),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("4",False)] fc t tc)
       ] t tc
multiState [("2",False),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",False),("4",True)] fc t tc)
       ] t tc
multiState [("2",False),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False),("4",True)] fc t tc)
       ] t tc
multiState [("2",False),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",False)] fc t tc)
       ] t tc
multiState [("2",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",False)] fc t tc)
       ] t tc
multiState [("2",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "2") [Bound 0 10000]) (multiState [("2",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("3",False),("4",False)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("4",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("3",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("4",True),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("3",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("3",False),("4",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("4",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("4",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("3",False)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("3",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("3",False)] fc t tc)
       ] t tc
multiState [("2",True),("3",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("2",True),("3",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("4",False),("5",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("4",False),("5",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("3",True),("4",False)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("4",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("4",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("3",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("3",True),("4",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("4",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("4",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("3",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("5",False)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("3",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True),("5",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("3",True)] fc t tc)
       ] t tc
multiState [("2",True),("3",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("3",True)] fc t tc)
       , Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("2",True)] fc t tc)
       ] t tc
multiState [("2",True),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("4",False)] fc t tc)
       ] t tc
multiState [("2",True),("4",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("2",True),("4",True)] fc t tc)
       ] t tc
multiState [("2",True),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True),("4",True)] fc t tc)
       ] t tc
multiState [("2",True),("4",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("2",True)] fc t tc)
       ] t tc
multiState [("2",True),("5",False)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("2",True),("5",True)] fc t tc)
       ] t tc
multiState [("2",True),("5",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("2",True)] fc t tc)
       ] t tc
multiState [("2",True)] fc t tc =
  When [ Case (Deposit "2" "2" ada (ChoiceValue (ChoiceId "1" "2"))) (multiState [] fc t tc)
       ] t tc
multiState [("3",False),("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("3",False),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("3",False),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("3",False),("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("3",False),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("3",False),("4",False)] fc t tc)
       ] t tc
multiState [("3",False),("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("3",False),("4",True)] fc t tc)
       ] t tc
multiState [("3",False),("4",True),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("3",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("3",False),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("3",False),("4",True),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("3",False),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("3",False),("4",True)] fc t tc)
       ] t tc
multiState [("3",False),("4",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("3",False)] fc t tc)
       ] t tc
multiState [("3",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("3",False),("5",True)] fc t tc)
       ] t tc
multiState [("3",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("3",False)] fc t tc)
       ] t tc
multiState [("3",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "3") [Bound 0 10000]) (multiState [("3",True)] fc t tc)
       ] t tc
multiState [("3",True),("4",False),("5",False)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("4",False),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("3",True),("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("3",True),("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("3",True),("4",False),("5",True)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("4",False),("5",True)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("3",True),("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("3",True),("4",False)] fc t tc)
       ] t tc
multiState [("3",True),("4",False)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("4",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("3",True),("4",True)] fc t tc)
       ] t tc
multiState [("3",True),("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("4",True),("5",False)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("3",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("3",True),("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("3",True),("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("4",True),("5",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("3",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("3",True),("4",True)] fc t tc)
       ] t tc
multiState [("3",True),("4",True)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("4",True)] fc t tc)
       , Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("3",True)] fc t tc)
       ] t tc
multiState [("3",True),("5",False)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("3",True),("5",True)] fc t tc)
       ] t tc
multiState [("3",True),("5",True)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("3",True)] fc t tc)
       ] t tc
multiState [("3",True)] fc t tc =
  When [ Case (Deposit "3" "3" ada (ChoiceValue (ChoiceId "1" "3"))) (multiState [] fc t tc)
       ] t tc
multiState [("4",False),("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("4",True),("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("4",False),("5",True)] fc t tc)
       ] t tc
multiState [("4",False),("5",True)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("4",True),("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("4",False)] fc t tc)
       ] t tc
multiState [("4",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "4") [Bound 0 10000]) (multiState [("4",True)] fc t tc)
       ] t tc
multiState [("4",True),("5",False)] fc t tc =
  When [ Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("5",False)] fc t tc)
       , Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("4",True),("5",True)] fc t tc)
       ] t tc
multiState [("4",True),("5",True)] fc t tc =
  When [ Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [("5",True)] fc t tc)
       , Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [("4",True)] fc t tc)
       ] t tc
multiState [("4",True)] fc t tc =
  When [ Case (Deposit "4" "4" ada (ChoiceValue (ChoiceId "1" "4"))) (multiState [] fc t tc)
       ] t tc
multiState [("5",False)] fc t tc =
  When [ Case (Choice (ChoiceId "1" "5") [Bound 0 10000]) (multiState [("5",True)] fc t tc)
       ] t tc
multiState [("5",True)] fc t tc =
  When [ Case (Deposit "5" "5" ada (ChoiceValue (ChoiceId "1" "5"))) (multiState [] fc t tc)
       ] t tc
multiState [] fc t tc = fc

