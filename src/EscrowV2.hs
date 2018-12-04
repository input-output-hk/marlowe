module EscrowV2 where

import Semantics

------------------------------------------
-- Implementation of an escrow contract --
------------------------------------------

-- The contract allows person 1 to pay 450 ADA
-- to person 2 by using person 3 as an escrow.
--
-- Person 1 can commit 450 ADA until block 100.
-- The payment will go through only if 2 out of the 3
-- participants choose the number "1".
--
-- If 2 out of the 3 participants chooses the number "0"
-- or if payment did not go through after block 100,
-- the money will be refunded to person 1.

alice, bob, carol :: Person
alice = 1
bob = 2
carol = 3

refund, pay :: ConcreteChoice

refund = 0
pay = 1

escrow :: Contract
escrow = CommitCash iCC1 alice
                    (Value 450)
                    10 100
                    (When (OrObs (majority_chose refund)
                                 (majority_chose pay))
                          90
                          (Choice (majority_chose pay)
                                  (Pay iP1 alice bob
                                       (Committed iCC1)
                                       100
                                       redeem_original)
                                  redeem_original)
                          redeem_original)
                    Null
  where majority_chose = two_chose alice bob carol

chose :: Integer -> ConcreteChoice -> Observation

chose per c = 
        PersonChoseThis (IdentChoice per) per c

one_chose :: Person -> Person -> ConcreteChoice -> Observation

one_chose per per' val = 
        (OrObs (chose per val) (chose per' val)) 
                                  
two_chose :: Person -> Person -> Person -> ConcreteChoice -> Observation

two_chose p1 p2 p3 c =
        OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))
              (AndObs (chose p2 c) (chose p3 c))

redeem_original :: Contract

redeem_original = RedeemCC iCC1 Null

iCC1 :: IdentCC

iCC1 = IdentCC 1

iP1 :: IdentPay

iP1 = IdentPay 1

