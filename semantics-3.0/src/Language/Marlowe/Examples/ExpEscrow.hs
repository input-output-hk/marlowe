{-# LANGUAGE OverloadedStrings #-}
module Language.Marlowe.Examples.ExpEscrow where

import Language.Marlowe

contract :: Contract
contract = When [Case (Deposit (AccountId 1 "party1") "party1" (Constant 450))
                      (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                  (When [Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                              Refund
                                        ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                              Refund
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                              100
                                              Refund)]
                                        100
                                        Refund)
                            ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                  (When [Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                              (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100 Refund)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                              (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                        100
                                        Refund)
                            ,Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                              Refund
                                        ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                              Refund
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                          100
                                                          Refund)]
                                        100 Refund)
                            ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                              (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                              (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                        100 Refund)
                            ,Case (Choice (ChoiceId "OK" "party3") [Interval 0 0])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                              Refund
                                        ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                              Refund
                                        ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)]
                                        100 Refund)
                            ,Case (Choice (ChoiceId "OK" "party3") [Interval 1 1])
                                  (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                              (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Interval 0 0])
                                              (When [Case (Choice (ChoiceId "OK" "party1") [Interval 0 0])
                                                          Refund
                                                    ,Case (Choice (ChoiceId "OK" "party1") [Interval 1 1])
                                                          (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                                    100
                                                    Refund)
                                        ,Case (Choice (ChoiceId "OK" "party2") [Interval 1 1])
                                              (Pay (AccountId 1 "party1") (Party "party2") (Constant 450) Refund)]
                                        100
                                        Refund)]
                            100
                            Refund)]
                10 Refund

