module Main where

import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import qualified Data.Maybe                    as Maybe
import           Control.Monad.State
import           Test.Tasty
import           Test.Tasty.QuickCheck
import           Test.Tasty.HUnit
import           Debug.Trace
import Data.Time

import           Semantics4
import           ZCBG2
import           ActusContracts

main :: IO ()
main = do
    print $ contractLifespan $ zeroCouponBondGuaranteed 1 2 3 1000 200 10 20
    now <- getCurrentTime
    let td = utctDay now
    putStrLn $ show $ genCouponBondContract 1 2 (cb td (addGregorianMonthsClip 4 td) 1000 0.05 )

account = (AccountId 1 1)
couponBond1 = When
    [ Case
          (Deposit account 1 (Constant 1000))
          (Pay
              account
              (Party 2)
              (AvailableMoney account)
              (When
                  [ Case
                        (Deposit account 2 (Constant 20))
                        (Pay
                            account
                            (Party 1)
                            (AvailableMoney account)
                            (When
                                [ Case
                                      (Deposit account 2 (Constant 20))
                                      (Pay
                                          account
                                          (Party 1)
                                          (AvailableMoney account)
                                          (When
                                              [ Case
                                                    (Deposit account 2 (Constant 1020))
                                                    (Pay account
                                                         (Party 1)
                                                         (AvailableMoney account)
                                                         RefundAll
                                                    )
                                              ]
                                              1574035189
                                              RefundAll
                                          )
                                      )
                                ]
                                1571356789
                                RefundAll
                            )
                        )
                  ]
                  1568764789
                  RefundAll
              )
          )
    ]
    1563407989
    RefundAll
