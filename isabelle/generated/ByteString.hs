{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ByteString(less_eq_ByteString) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

less_eq_ByteString :: String -> String -> Bool;
less_eq_ByteString a b = a <= b;

}
