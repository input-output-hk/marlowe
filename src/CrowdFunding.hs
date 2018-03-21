module CrowdFunding where

import Semantics    

-------------------------------------------------
-- Implementation of a "limited crowd"-funding --
-------------------------------------------------

-- The contract allows a person 5 to collect 1000 ADA
-- by inviting 4 people to donate.
-- People 1 to 4 can first choose how much to donate
-- and then commit that ammount of money until
-- block 20. At block 10, if the ammount collected
-- is equal or higher than 1000 ADA, person 5 will
-- have until block 20 to claim all of it.
-- In any case, people 1 to 4 will be able to redeem
-- unclaimed money after block 20.

crowdFunding :: Contract
crowdFunding = Both (Both (Both (When (AndObs (PersonChoseSomething (IdentChoice 1) 1)
                                               (ValueGE (MoneyFromChoice (IdentChoice 1) 1
                                                                         (ConstMoney 0))
                                                        (ConstMoney 1)))
                                       10
                                       (CommitCash (IdentCC 1) 1
                                                   (MoneyFromChoice (IdentChoice 1) 1
                                                                    (ConstMoney 0))
                                                   10 20 Null Null)
                                       Null)
                                 (When (AndObs (PersonChoseSomething (IdentChoice 2) 2)
                                               (ValueGE (MoneyFromChoice (IdentChoice 2) 2
                                                                         (ConstMoney 0))
                                                        (ConstMoney 1)))
                                       10
                                       (CommitCash (IdentCC 2) 2
                                                   (MoneyFromChoice (IdentChoice 2) 2
                                                                    (ConstMoney 0))
                                                   10 20 Null Null)
                                       Null))
                           (Both (When (AndObs (PersonChoseSomething (IdentChoice 3) 3)
                                               (ValueGE (MoneyFromChoice (IdentChoice 3) 3
                                                                         (ConstMoney 0))
                                                        (ConstMoney 1)))
                                       10
                                       (CommitCash (IdentCC 3) 3
                                                   (MoneyFromChoice (IdentChoice 3) 3
                                                                    (ConstMoney 0))
                                                   10 20 Null Null)
                                       Null)
                                 (When (AndObs (PersonChoseSomething (IdentChoice 4) 4)
                                               (ValueGE (MoneyFromChoice (IdentChoice 4) 4
                                                                         (ConstMoney 0))
                                                        (ConstMoney 1)))
                                       10
                                       (CommitCash (IdentCC 4) 4
                                                   (MoneyFromChoice (IdentChoice 4) 4
                                                                    (ConstMoney 0))
                                                   10 20 Null Null)
                                       Null)))
                     (When FalseObs 10 Null
                           (Choice (ValueGE (AddMoney (AddMoney (MoneyFromChoice (IdentChoice 1) 1
                                                                                 (ConstMoney 0))
                                                                (MoneyFromChoice (IdentChoice 2) 2
                                                                                 (ConstMoney 0)))
                                                      (AddMoney (MoneyFromChoice (IdentChoice 3) 3
                                                                                 (ConstMoney 0))
                                                                (MoneyFromChoice (IdentChoice 4) 4
                                                                                 (ConstMoney 0))))
                                            (ConstMoney 1000))
                                   (Both (Both (Pay (IdentPay 1) 1 5
                                                    (AvailableMoney (IdentCC 1))
                                                    20 Null)
                                               (Pay (IdentPay 2) 2 5
                                                    (AvailableMoney (IdentCC 2))
                                                    20 Null))
                                         (Both (Pay (IdentPay 3) 3 5
                                                    (AvailableMoney (IdentCC 3))
                                                    20 Null)
                                               (Pay (IdentPay 4) 4 5
                                                    (AvailableMoney (IdentCC 4))
                                                    20 Null)))
                                   Null))
