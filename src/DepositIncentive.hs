module DepositIncentive where


import Semantics    

-----------------------------------------------------
-- Implementation of a deposit incentive mechanism --
-----------------------------------------------------

-- The contract allows alice to deposit 100 ADA
-- before block 10 and bib to deposit 20 ADA
-- before block 20. Alice can retrieve the 100 ADA
-- at any moment in time, cancelling the contract.
-- If Alice keeps the money up to block 100,
-- Alice gets to keep the 20 ADA from bob.

depositIncentive :: Contract
depositIncentive = 
  CommitCash com1 alice ada100 10 200
             (CommitCash com2 bob ada20 20 200
                         (When (PersonChoseSomething choice1 alice) 100
                               (Both (RedeemCC com1 Null) (RedeemCC com2 Null))
                               (Pay pay1 bob alice ada20 200
                                    (Both (RedeemCC com1 Null) (RedeemCC com2 Null))))
                         (RedeemCC com1 Null))
             Null

-- Nomenclauture used in the contract

alice = 1
bob   = 2

ada100 = ConstMoney 100
ada20  = ConstMoney 20

pay1 = IdentPay 1

com1 = IdentCC 1
com2 = IdentCC 2

choice1 = IdentChoice 1