{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module MList(empty, delete, insert, lookup, member, findWithDefault) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Option;
import qualified Orderings;

empty :: forall a b. (Orderings.Linorder a) => [(a, b)];
empty = [];

delete :: forall a b. (Eq a, Orderings.Linorder a) => a -> [(a, b)] -> [(a, b)];
delete a [] = [];
delete a ((x, y) : z) =
  (if a == x then z
    else (if Orderings.less x a then (x, y) : delete a z else (x, y) : z));

insert :: forall a b. (Orderings.Linorder a) => a -> b -> [(a, b)] -> [(a, b)];
insert a b [] = [(a, b)];
insert a b ((x, y) : z) =
  (if Orderings.less a x then (a, b) : (x, y) : z
    else (if Orderings.less x a then (x, y) : insert a b z else (x, b) : z));

lookup :: forall a b. (Eq a, Orderings.Linorder a) => a -> [(a, b)] -> Maybe b;
lookup a [] = Nothing;
lookup a ((x, y) : z) =
  (if a == x then Just y
    else (if Orderings.less x a then lookup a z else Nothing));

member :: forall a b. (Eq a, Orderings.Linorder a) => a -> [(a, b)] -> Bool;
member k d = not (Option.is_none (lookup k d));

findWithDefault ::
  forall a b. (Eq b, Orderings.Linorder b) => a -> b -> [(b, a)] -> a;
findWithDefault d k l = (case lookup k l of {
                          Nothing -> d;
                          Just x -> x;
                        });

}
