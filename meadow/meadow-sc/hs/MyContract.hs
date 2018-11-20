module MyContract(contract) where

import Marlowe

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Escrow example using embedding

contract :: Contract
contract = CommitCash (IdentCC 1) 1
                      (ConstMoney 100)
                      10 200
                      (CommitCash (IdentCC 2) 2
                                  (ConstMoney 20)
                                  20 200
                                  (When (PersonChoseSomething (IdentChoice 1) 1)
                                        100
                                        (Both (RedeemCC (IdentCC 1) Null)
                                              (RedeemCC (IdentCC 2) Null))
                                        (Pay (IdentPay 1) 2 1
                                             (ConstMoney 20)
                                             200
                                             (Both (RedeemCC (IdentCC 1) Null)
                                                   (RedeemCC (IdentCC 2) Null))))
                                  (RedeemCC (IdentCC 1) Null))
                      Null

