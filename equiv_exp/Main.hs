module Main where

import Data.Time
import ACTUS

main = do
    now <- getCurrentTime
    let td = utctDay now
    putStrLn $ show $ schedule ((singleEvent td) {
        scheduleEnd = Just (addDays 10000 td), scheduleCycle = Just $ Cycle 100 Day LongLastStub})
    putStrLn "Test"