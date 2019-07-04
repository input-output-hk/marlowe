module Main where

import Data.Time
import ACTUS

main = do
    now <- getCurrentTime
    let td = utctDay now
    putStrLn $ show $ genZcbContract 1 2 (zcb td (addGregorianYearsClip 1 td) 1000 20 )
    putStrLn $ show $ genCouponBondContract 1 2 (cb td (addGregorianMonthsClip 2 td) 1000 0.05 )
    putStrLn "Test"