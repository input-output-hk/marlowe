module Language.Marlowe.Examples.ExpCrowdFunding where

import           Language.Marlowe

contract :: Contract
contract = crowdfunding 1000 100

-- Limited crowdfunding example using embedding
crowdfunding :: Money -> Timeout -> Contract
crowdfunding target tim =
  multiState [(2,False),(3,False),(4,False),(5,False)] cont tim cont
  where cont = If (ValueGE (AddValue (AddValue (AvailableMoney (AccountId 1 2))
                                               (AvailableMoney (AccountId 1 3)))
                                     (AddValue (AvailableMoney (AccountId 1 4))
                                               (AvailableMoney (AccountId 1 5))))
                           (Constant target))
                  (Pay (AccountId 1 2) (Account creatorAcc) (AvailableMoney (AccountId 1 2))
                       (Pay (AccountId 1 3) (Account creatorAcc) (AvailableMoney (AccountId 1 3))
                            (Pay (AccountId 1 4) (Account creatorAcc) (AvailableMoney (AccountId 1 4))
                                 (Pay (AccountId 1 5) (Account creatorAcc) (AvailableMoney (AccountId 1 5))
                                      Refund))))
                  Refund
        creatorAcc = AccountId 1 1

-- Defines a state machine for each contributor:
-- (party, False) - Has not chosen the amount to contribute
-- (party, True) - Has chosen the amount and is ready to make the deposit
type ContributionState = (Party, Bool)

multiState :: [ContributionState] -> Contract -> Integer -> Contract -> Contract
multiState [(2,False),(3,False),(4,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(3,False),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(3,False),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,False),(4,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(3,False),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(3,False),(4,False)] fc t tc)
       ] t tc
multiState [(2,False),(3,False),(4,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(3,False),(4,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,False),(4,True),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(3,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(3,False),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,False),(4,True),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(4,True),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(3,False),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(3,False),(4,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,False),(4,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(4,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(3,False)] fc t tc)
       ] t tc
multiState [(2,False),(3,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(3,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(3,False)] fc t tc)
       ] t tc
multiState [(2,False),(3,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,False),(3,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(4,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(4,False),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(3,True),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(3,True),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(4,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(4,False),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(3,True),(4,False)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(4,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(4,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(3,True),(4,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(4,True),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(3,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(3,True),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(4,True),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(3,True),(4,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(4,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(3,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(3,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(3,True)] fc t tc)
       ] t tc
multiState [(2,False),(3,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(3,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,False)] fc t tc)
       ] t tc
multiState [(2,False),(4,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(4,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(4,False)] fc t tc)
       ] t tc
multiState [(2,False),(4,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,False),(4,True)] fc t tc)
       ] t tc
multiState [(2,False),(4,True),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(4,True),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False),(4,True)] fc t tc)
       ] t tc
multiState [(2,False),(4,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,False)] fc t tc)
       ] t tc
multiState [(2,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,False)] fc t tc)
       ] t tc
multiState [(2,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 2) [(0,10000)]) (multiState [(2,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(4,False),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(3,False),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(3,False),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(4,False),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(3,False),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(3,False),(4,False)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(4,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(3,False),(4,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(4,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(3,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(3,False),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(4,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(4,True),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(3,False),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(3,False),(4,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(4,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(4,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(3,False)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(3,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,False),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(3,False)] fc t tc)
       ] t tc
multiState [(2,True),(3,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,False)] fc t tc)
       , Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(2,True),(3,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(4,False),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(4,False),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(3,True),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(3,True),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(4,False),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(4,False),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(3,True),(4,False)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(4,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(4,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(3,True),(4,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(4,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(3,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(3,True),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(4,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(3,True),(4,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(4,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(3,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(3,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(3,True)] fc t tc)
       ] t tc
multiState [(2,True),(3,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(3,True)] fc t tc)
       , Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(2,True)] fc t tc)
       ] t tc
multiState [(2,True),(4,False),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(4,False),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(4,False)] fc t tc)
       ] t tc
multiState [(2,True),(4,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(2,True),(4,True)] fc t tc)
       ] t tc
multiState [(2,True),(4,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(4,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True),(4,True)] fc t tc)
       ] t tc
multiState [(2,True),(4,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(2,True)] fc t tc)
       ] t tc
multiState [(2,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(2,True),(5,True)] fc t tc)
       ] t tc
multiState [(2,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(2,True)] fc t tc)
       ] t tc
multiState [(2,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 2) 2 (ChoiceValue (ChoiceId 1 2) (Constant 0))) (multiState [] fc t tc)
       ] t tc
multiState [(3,False),(4,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(3,False),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(3,False),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(3,False),(4,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(3,False),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(3,False),(4,False)] fc t tc)
       ] t tc
multiState [(3,False),(4,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(3,False),(4,True)] fc t tc)
       ] t tc
multiState [(3,False),(4,True),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(3,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(3,False),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(3,False),(4,True),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(3,False),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(3,False),(4,True)] fc t tc)
       ] t tc
multiState [(3,False),(4,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(3,False)] fc t tc)
       ] t tc
multiState [(3,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(3,False),(5,True)] fc t tc)
       ] t tc
multiState [(3,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(3,False)] fc t tc)
       ] t tc
multiState [(3,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 3) [(0,10000)]) (multiState [(3,True)] fc t tc)
       ] t tc
multiState [(3,True),(4,False),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(4,False),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(3,True),(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(3,True),(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(3,True),(4,False),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(4,False),(5,True)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(3,True),(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(3,True),(4,False)] fc t tc)
       ] t tc
multiState [(3,True),(4,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(4,False)] fc t tc)
       , Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(3,True),(4,True)] fc t tc)
       ] t tc
multiState [(3,True),(4,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(4,True),(5,False)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(3,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(3,True),(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(3,True),(4,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(3,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(3,True),(4,True)] fc t tc)
       ] t tc
multiState [(3,True),(4,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(4,True)] fc t tc)
       , Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(3,True)] fc t tc)
       ] t tc
multiState [(3,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(3,True),(5,True)] fc t tc)
       ] t tc
multiState [(3,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(3,True)] fc t tc)
       ] t tc
multiState [(3,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 3) 3 (ChoiceValue (ChoiceId 1 3) (Constant 0))) (multiState [] fc t tc)
       ] t tc
multiState [(4,False),(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(4,True),(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(4,False),(5,True)] fc t tc)
       ] t tc
multiState [(4,False),(5,True)] fc t tc =
  When [ Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(4,True),(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(4,False)] fc t tc)
       ] t tc
multiState [(4,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 4) [(0,10000)]) (multiState [(4,True)] fc t tc)
       ] t tc
multiState [(4,True),(5,False)] fc t tc =
  When [ Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(5,False)] fc t tc)
       , Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(4,True),(5,True)] fc t tc)
       ] t tc
multiState [(4,True),(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [(5,True)] fc t tc)
       , Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [(4,True)] fc t tc)
       ] t tc
multiState [(4,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 4) 4 (ChoiceValue (ChoiceId 1 4) (Constant 0))) (multiState [] fc t tc)
       ] t tc
multiState [(5,False)] fc t tc =
  When [ Case (Choice (ChoiceId 1 5) [(0,10000)]) (multiState [(5,True)] fc t tc)
       ] t tc
multiState [(5,True)] fc t tc =
  When [ Case (Deposit (AccountId 1 5) 5 (ChoiceValue (ChoiceId 1 5) (Constant 0))) (multiState [] fc t tc)
       ] t tc
multiState [] fc t tc = fc

