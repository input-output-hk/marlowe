module Escrow where

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

escrow :: Contract
escrow = CommitCash (IdentCC 1) 1
                    (ConstMoney 450)
                    10 100
                    (When (OrObs (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 0)
                                                (OrObs (PersonChoseThis (IdentChoice 2) 2 0)
                                                       (PersonChoseThis (IdentChoice 3) 3 0)))
                                        (AndObs (PersonChoseThis (IdentChoice 2) 2 0)
                                                (PersonChoseThis (IdentChoice 3) 3 0)))
                                 (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                                (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                                       (PersonChoseThis (IdentChoice 3) 3 1)))
                                        (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                                (PersonChoseThis (IdentChoice 3) 3 1))))
                          90
                          (Choice (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                                 (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                                        (PersonChoseThis (IdentChoice 3) 3 1)))
                                         (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                                 (PersonChoseThis (IdentChoice 3) 3 1)))
                                  (Pay (IdentPay 1) 1 2
                                       (AvailableMoney (IdentCC 1))
                                       100
                                       (RedeemCC (IdentCC 1) Null))
                                  (RedeemCC (IdentCC 1) Null))
                          (RedeemCC (IdentCC 1) Null))
                    Null
