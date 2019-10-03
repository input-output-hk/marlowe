module CrowdFunding where

import Semantics    

-------------------------------------------------
-- Implementation of a "limited crowd"-funding --
-------------------------------------------------

-- The contract allows a person 5 to collect 1000 ADA
-- by inviting 4 people to donate.
-- People 1 to 4 can first choose how much to donate
-- and then commit that amount of money until
-- block 20. At block 10, if the amount collected
-- is equal or higher than 1000 ADA, person 5 will
-- have until block 20 to claim all of it.
-- In any case, people 1 to 4 will be able to redeem
-- unclaimed money after block 20.

crowdFunding :: Contract
crowdFunding = Both (Both (Both (When (AndObs (PersonChoseSomething (IdentChoice 1) 1)
                                              (ValueGE (ValueFromChoice (IdentChoice 1) 1
                                                                        (Value 0))
                                                       (Value 1)))
                                      10
                                      (CommitCash (IdentCC 1) 1
                                                  (ValueFromChoice (IdentChoice 1) 1
                                                                   (Value 0))
                                                  10 20 Null Null)
                                      Null)
                                (When (AndObs (PersonChoseSomething (IdentChoice 2) 2)
                                              (ValueGE (ValueFromChoice (IdentChoice 2) 2
                                                                        (Value 0))
                                                       (Value 1)))
                                      10
                                      (CommitCash (IdentCC 2) 2
                                                  (ValueFromChoice (IdentChoice 2) 2
                                                                   (Value 0))
                                                  10 20 Null Null)
                                      Null))
                          (Both (When (AndObs (PersonChoseSomething (IdentChoice 3) 3)
                                              (ValueGE (ValueFromChoice (IdentChoice 3) 3
                                                                        (Value 0))
                                                       (Value 1)))
                                      10
                                      (CommitCash (IdentCC 3) 3
                                                  (ValueFromChoice (IdentChoice 3) 3
                                                                   (Value 0))
                                                  10 20 Null Null)
                                      Null)
                                (When (AndObs (PersonChoseSomething (IdentChoice 4) 4)
                                              (ValueGE (ValueFromChoice (IdentChoice 4) 4
                                                                        (Value 0))
                                                       (Value 1)))
                                      10
                                      (CommitCash (IdentCC 4) 4
                                                  (ValueFromChoice (IdentChoice 4) 4
                                                                   (Value 0))
                                                  10 20 Null Null)
                                      Null)))
                    (When FalseObs 10 Null
                          (Choice (ValueGE (AddValue (AddValue (Committed (IdentCC 1))
                                                               (Committed (IdentCC 2)))
                                                     (AddValue (Committed (IdentCC 3))
                                                               (Committed (IdentCC 4))))
                                           (Value 1000))
                                  (Both (Both (Pay (IdentPay 1) 1 5
                                                   (Committed (IdentCC 1))
                                                   20 Null)
                                              (Pay (IdentPay 2) 2 5
                                                   (Committed (IdentCC 2))
                                                   20 Null))
                                        (Both (Pay (IdentPay 3) 3 5
                                                   (Committed (IdentCC 3))
                                                   20 Null)
                                              (Pay (IdentPay 4) 4 5
                                                   (Committed (IdentCC 4))
                                                   20 Null)))
                                  Null))

