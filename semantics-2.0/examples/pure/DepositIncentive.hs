module DepositIncentive where

import Semantics

depositIncentive = Commit 1 1 1 
                     (Constant 100) 10 200 
                     (Commit 2 2 2 
                        (Constant 20) 20 200 
                        (When 
                           (ChoseSomething (1, 1)) 100 
                           (Both 
                              (Pay 3 1 1 
                                 (Constant 100) 200 Null Null) 
                              (Pay 4 2 2 
                                 (Constant 20) 200 Null Null)) 
                           (Both 
                              (Pay 5 1 1 
                                 (Constant 100) 200 Null Null) 
                              (Pay 6 2 1 
                                 (Constant 20) 200 Null Null))) 
                        (Pay 7 1 1 
                           (Constant 100) 200 Null Null)) Null
