{-# LANGUAGE OverloadedLists #-}
module FSMap where

import Data.SBV
import Data.SBV.Tuple as ST
import Data.SBV.List as SL
import Data.SBV.Maybe as SM

type FSMap a b = SList (a, b)

empty :: Ord a => SymVal a => SymVal b => FSMap a b
empty = [] 

insert :: Ord a => SymVal a => SymVal b => Integer ->
          SBV a -> SBV b -> FSMap a b -> FSMap a b 
insert b k v s
  | b <= 0 = [] 
  | otherwise = ite (SL.null s)
                    (SL.singleton nh)
                    (ite (k .> h)
                         (oh .: (insert (b - 1) k v t))
                         (ite (k .< h)
                              (nh .: s)
                              (nh .: t)))
  where oh = SL.head s
        (h, _) = ST.untuple $ oh
        t = SL.tail s
        nh = ST.tuple (k, v)

lookup :: Ord a => SymVal a => SymVal b => Integer ->
          SBV a -> FSMap a b -> SMaybe b
lookup b k s
  | b <= 0 = sNothing
  | otherwise = ite (SL.null s)
                    SM.sNothing
                    (ite (k .> h)
                         (FSMap.lookup (b - 1) k t)
                         (ite (k .== h)
                              (SM.sJust h2)
                              (SM.sNothing)))
  where (h, h2) = ST.untuple $ SL.head s
        t = SL.tail s

size :: Ord a => SymVal a => SymVal b => FSMap a b -> SInteger
size s = SL.length s

delete :: Ord a => SymVal a => SymVal b => Integer ->
          SBV a -> FSMap a b -> FSMap a b
delete b v s
  | b <= 0 = s
  | otherwise = ite (SL.null s)
                    [] 
                    (ite (v .< h1)
                         s
                         (ite (v .== h1)
                              t
                              (h .: (delete (b - 1) v t))))
  where h = SL.head s
        (h1, _) = ST.untuple h
        t = SL.tail s

valid_aux :: Ord a => SymVal a => SymVal b => Integer -> SBV a -> FSMap a b -> SBool
valid_aux b v s
  | b <= 0 = sFalse
  | otherwise = ite (SL.null s)
                    sTrue
                    (ite (v .< h)
                         (valid_aux (b - 1) h t)
                         sFalse)
  where (h, _) = ST.untuple $ SL.head s
        t = SL.tail s

valid :: Ord a => SymVal a => SymVal b => Integer -> FSMap a b -> SBool
valid b s
  | b <= 0 = sFalse
  | otherwise = ite (SL.null s)
                    sTrue
                    (valid_aux b (fst $ ST.untuple $ SL.head s) (SL.tail s))


