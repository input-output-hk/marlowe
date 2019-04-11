module CrowdFunding where

import Semantics

crowdFunding = Both 
                 (Both 
                    (Both 
                       (When 
                          (AndObs 
                             (ChoseSomething (1, 1)) 
                             (ValueGE 
                                (ValueFromChoice (1, 1) 
                                   (Constant 0)) 
                                (Constant 1))) 10 
                          (Commit 1 1 1 
                             (ValueFromChoice (1, 1) 
                                (Constant 0)) 10 20 Null Null) Null) 
                       (When 
                          (AndObs 
                             (ChoseSomething (1, 2)) 
                             (ValueGE 
                                (ValueFromChoice (1, 2) 
                                   (Constant 0)) 
                                (Constant 1))) 10 
                          (Commit 2 2 2 
                             (ValueFromChoice (1, 2) 
                                (Constant 0)) 10 20 Null Null) Null)) 
                    (Both 
                       (When 
                          (AndObs 
                             (ChoseSomething (1, 3)) 
                             (ValueGE 
                                (ValueFromChoice (1, 3) 
                                   (Constant 0)) 
                                (Constant 1))) 10 
                          (Commit 3 3 3 
                             (ValueFromChoice (1, 3) 
                                (Constant 0)) 10 20 Null Null) Null) 
                       (When 
                          (AndObs 
                             (ChoseSomething (1, 4)) 
                             (ValueGE 
                                (ValueFromChoice (1, 4) 
                                   (Constant 0)) 
                                (Constant 1))) 10 
                          (Commit 4 4 4 
                             (ValueFromChoice (1, 4) 
                                (Constant 0)) 10 20 Null Null) Null))) 
                 (When FalseObs 10 Null 
                    (Choice 
                       (ValueGE 
                          (AddValue 
                             (AddValue 
                                (Committed 1) 
                                (Committed 2)) 
                             (AddValue 
                                (Committed 3) 
                                (Committed 4))) 
                          (Constant 1000)) 
                       (Both 
                          (Both 
                             (Pay 5 1 5 
                                (Committed 1) 20 Null Null) 
                             (Pay 6 2 5 
                                (Committed 2) 20 Null Null)) 
                          (Both 
                             (Pay 7 3 5 
                                (Committed 3) 20 Null Null) 
                             (Pay 8 4 5 
                                (Committed 4) 20 Null Null))) Null))
               
