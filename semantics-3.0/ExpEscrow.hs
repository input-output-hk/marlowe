module ExpEscrow where

import Marlowe

contract :: Contract
contract = When [Case (Deposit (AccountId 1 1) 1 (Constant 450))
                      (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                  (When [Case (Choice (ChoiceId 1 2) [(0,0)])
                                              Refund
                                        ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                              (When [Case (Choice (ChoiceId 1 3) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 3) [(0,0)])
                                              Refund
                                        ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                              (When [Case (Choice (ChoiceId 1 2) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                              100
                                              Refund)]
                                        100
                                        Refund)
                            ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                  (When [Case (Choice (ChoiceId 1 2) [(0,0)])
                                              (When [Case (Choice (ChoiceId 1 3) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                              (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)
                                        ,Case (Choice (ChoiceId 1 3) [(0,0)])
                                              (When [Case (Choice (ChoiceId 1 2) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100 Refund)
                                        ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                              (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                        100
                                        Refund)
                            ,Case (Choice (ChoiceId 1 2) [(0,0)])
                                  (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                              Refund
                                        ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                              (When [Case (Choice (ChoiceId 1 3) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 3) [(0,0)])
                                              Refund
                                        ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                              (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                          100
                                                          Refund)]
                                        100 Refund)
                            ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                  (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                              (When [Case (Choice (ChoiceId 1 3) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                              (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)
                                        ,Case (Choice (ChoiceId 1 3) [(0,0)])
                                              (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                              (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                        100 Refund)
                            ,Case (Choice (ChoiceId 1 3) [(0,0)])
                                  (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                              Refund
                                        ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                              (When [Case (Choice (ChoiceId 1 2) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 2) [(0,0)])
                                              Refund
                                        ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                              (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)]
                                        100 Refund)
                            ,Case (Choice (ChoiceId 1 3) [(1,1)])
                                  (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                              (When [Case (Choice (ChoiceId 1 2) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                              (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)
                                        ,Case (Choice (ChoiceId 1 2) [(0,0)])
                                              (When [Case (Choice (ChoiceId 1 1) [(0,0)])
                                                          Refund
                                                    ,Case (Choice (ChoiceId 1 1) [(1,1)])
                                                          (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId 1 2) [(1,1)])
                                              (Pay (AccountId 1 1) (Party 2) (Constant 450) Refund)]
                                        100
                                        Refund)]
                            100
                            Refund)]
                10 Refund

