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


-- escrow :: Contract
-- escrow = CommitCash 1
--                     (ConstMoney 450)
--                     (When (OrObs (two_chose 1 2 3 refund)
--                                  (two_chose 1 2 3 pay))
--                           (Choice (two_chose 1 2 3 pay)
--                                   (Pay 1 2 AvailableMoney)
--                                   redeem_original))   

-- refund = 0
-- pay    = 1


escrow :: Contract
escrow = CommitCash iCC1 1
                    (ConstMoney 450)
                    10 100
                    (When (OrObs (two_chose 1 2 3 0)
                                 (two_chose 1 2 3 1))
                          90
                          (Choice (two_chose 1 2 3 1)
                                  (Pay iP1 1 2
                                       (AvailableMoney iCC1)
                                       100
                                       redeem_original)
                                  redeem_original)
                          redeem_original)
                    Null

chose :: Int -> ConcreteChoice -> Observation

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
