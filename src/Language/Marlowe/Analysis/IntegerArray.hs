{-# LANGUAGE OverloadedLists #-}
module Language.Marlowe.Analysis.IntegerArray where

import Prelude hiding (all, lookup)
import Data.SBV
import Data.SBV.Tuple as ST
import Data.SBV.List as SL
import Data.SBV.Maybe as SM

type NIntegerArray = [Maybe Integer]
type IntegerArray = SList (Maybe Integer)

empty :: Integer -> IntegerArray
empty b = emptyAux 1 b
  where emptyAux b mb
         | b > mb = []
         | otherwise = (sNothing .: emptyAux (b + 1) mb)

insert :: Integer -> SInteger -> IntegerArray -> IntegerArray
insert k v s = insertAux 1 k v s
  where insertAux b k v s
         | b >= k = (sJust v) .: (SL.tail s)
         | otherwise = (SL.head s) .: (insertAux (b + 1) k v (SL.tail s))

lookup :: Integer -> IntegerArray -> SMaybe Integer
lookup k s = lookupAux 1 k s
  where lookupAux b k s
         | b >= k = SL.head s
         | otherwise = lookupAux (b + 1) k (SL.tail s)

member :: Integer -> IntegerArray -> SBool
member k s = SM.isJust $ lookup k s

findWithDefault :: Integer -> Integer -> IntegerArray -> SInteger 
findWithDefault def k s = SM.maybe (literal def) id (lookup k s)

delete :: Integer -> IntegerArray -> IntegerArray
delete k s = deleteAux 1 k s
  where deleteAux b k s
         | b >= k = (sNothing) .: (SL.tail s)
         | otherwise = (SL.head s) .: (deleteAux (b + 1) k (SL.tail s))

valid :: Integer -> IntegerArray -> SBool
valid k s = SL.length s .== (literal k)

all :: Integer -> (SInteger -> SBool) -> IntegerArray -> SBool
all b f s = allAux 1 b f s
  where allAux b mb f s
         | b > mb = sTrue
         | otherwise = (SM.maybe sTrue f (SL.head s)) .&& (allAux (b + 1) mb f (SL.tail s))

unionWith :: Integer -> (SInteger -> SInteger -> SInteger) -> IntegerArray -> IntegerArray
          -> IntegerArray
unionWith b f s1 s2 = unionWithAux 1 b f s1 s2
  where unionWithAux b mb f s1 s2
         | b > mb = []
         | otherwise = nh .: (unionWithAux (b + 1) mb f (SL.tail s1) (SL.tail s2))
             where nh = SM.maybe (SL.head s2)
                                 (\x -> SM.maybe (SL.head s1)
                                                 (\y -> sJust $ f x y)
                                                 (SL.head s2))
                                 (SL.head s1)

minViewWithKey :: Integer -> IntegerArray -> SMaybe ((Integer, Integer), NIntegerArray)
minViewWithKey b s = minViewWithKeyAux 1 b s

minViewWithKeyAux :: Integer -> Integer -> IntegerArray
                  -> SMaybe ((Integer, Integer), NIntegerArray)
minViewWithKeyAux b mb s
 | b > mb = sNothing
 | otherwise = SM.maybe (minViewWithKeyAux (b + 1) mb (SL.tail s))
                        (\x -> sJust $ ST.tuple (ST.tuple (literal b, x), SL.tail s))
                        (SL.head s)

