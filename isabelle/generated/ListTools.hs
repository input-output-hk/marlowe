{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ListTools(anya) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

anya :: forall a. (a -> Bool) -> [a] -> Bool;
anya f [] = False;
anya f (h : t) = f h || anya f t;

}
