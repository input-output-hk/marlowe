{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Division(quot) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;

quot :: Arith.Int -> Arith.Int -> Arith.Int;
quot x y =
  (if Arith.less_int x Arith.zero_int == Arith.less_int y Arith.zero_int
    then Arith.divide_int x y
    else Arith.uminus_int
           (Arith.divide_int (Arith.abs_int x) (Arith.abs_int y)));

}
