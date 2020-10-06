{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.ExpEscrow where

import Language.Marlowe

contract :: Contract
contract = When [Case (Deposit ("party1") "party1" (Constant 450))
                      (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                  (When [Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                              Close
                                        ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                              Close
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                              100
                                              Close)]
                                        100
                                        Close)
                            ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                  (When [Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                              (Pay ("party1") (Party "party2") (Constant 450) Close)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100 Close)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                              (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                        100
                                        Close)
                            ,Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                              Close
                                        ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                              Close
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                          100
                                                          Close)]
                                        100 Close)
                            ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                              (Pay ("party1") (Party "party2") (Constant 450) Close)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                              (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                        100 Close)
                            ,Case (Choice (ChoiceId "OK" "party3") [Bound 0 0])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                              Close
                                        ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                              Close
                                        ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)]
                                        100 Close)
                            ,Case (Choice (ChoiceId "OK" "party3") [Bound 1 1])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                              (Pay ("party1") (Party "party2") (Constant 450) Close)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Bound 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Bound 0 0])
                                                          Close
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Bound 1 1])
                                                          (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                                    100
                                                    Close)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Bound 1 1])
                                              (Pay ("party1") (Party "party2") (Constant 450) Close)]
                                        100
                                        Close)]
                            100
                            Close)]
                10 Close

