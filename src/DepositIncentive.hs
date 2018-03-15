module DepositIncentive where


import Semantics    

-----------------------------------------------------
-- Implementation of a deposit incentive mechanism --
-----------------------------------------------------

-- The contract allows person 1 to deposit 100 ADA
-- before block 10 and person 2 to deposit 20 ADA
-- before block 20. Person 1 can retrieve the 100 ADA
-- at any moment in time, cancelling the contract.
-- If person 1 keeps the money up to block 100,
-- person 1 gets to keep the 20 ADA from person 2.

depositIncentive :: Contract
depositIncentive = CommitCash (IdentCC 1) 1 100 10 200
                              (CommitCash (IdentCC 2) 2 20 20 200
                                          (When (PersonChoseSomething (IdentChoice 1) 1)
                                                100
                                                (Both (RedeemCC (IdentCC 1) Null)
                                                      (RedeemCC (IdentCC 2) Null))
                                                (Pay (IdentPay 1) 2 1 20 200
                                                     (Both (RedeemCC (IdentCC 1) Null)
                                                           (RedeemCC (IdentCC 2) Null))))
                                          (RedeemCC (IdentCC 1) Null))
                              Null
