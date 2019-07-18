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
    let couponBondFor6Month12PercentConfig = cb td (addGregorianMonthsClip 6 td) 1000 0.12
    print $ genCouponBondContract 1 2 couponBondFor6Month12PercentConfig

acc = AccountId 1 1
investor = Party 1
issuer = Party 2
couponBondFor6Month12Percent = When
    [ Case
        (Deposit acc 1 (Constant 1000))
        (Pay acc issuer (Constant 1000)
            (When
                [ Case
                    (Deposit acc 2 (Constant 10))
                    (Pay acc investor (Constant 10)
                        (When
                            [ Case
                                (Deposit acc 2 (Constant 10))
                                (Pay acc investor (Constant 10)
                                    (When
                                        [ Case
                                            (Deposit acc 2 (Constant 10))
                                            (Pay acc investor (Constant 10)
                                                (When
                                                    [ Case
                                                        (Deposit acc 2 (Constant 10))
                                                        (Pay acc investor (Constant 10)
                                                            (When
                                                                [ Case
                                                                    (Deposit acc 2 (Constant 10))
                                                                    (Pay acc investor (Constant 10)
                                                                        (When
                                                                            [ Case
                                                                                (Deposit acc 2 (Constant 1010))
                                                                                (Pay acc investor (Constant 1010) RefundAll)
                                                                            ]
                                                                            1579305589
                                                                            RefundAll
                                                                        )
                                                                    )
                                                                ]
                                                                1576627189
                                                                RefundAll
                                                            )
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
                1566086389
                RefundAll
            )
        )
    ]
    1563407989
    RefundAll
