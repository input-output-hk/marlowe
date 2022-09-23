{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Numeral_Type(Bit0, Num1) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;
import qualified Finite_Set;

newtype Bit0 a = Abs_bit0 Arith.Int;

data Num1 = One_num1;

}
