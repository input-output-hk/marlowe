{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SList(empty, insert) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Orderings;

empty :: forall a. (Orderings.Linorder a) => [a];
empty = [];

insert :: forall a. (Orderings.Linorder a) => a -> [a] -> [a];
insert a [] = [a];
insert a (x : z) =
  (if Orderings.less a x then a : x : z
    else (if Orderings.less x a then x : insert a z else x : z));

}
