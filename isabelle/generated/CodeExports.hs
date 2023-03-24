{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CodeExports(eq_export_helper_int) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;

eq_wrap :: forall a. (Eq a) => a -> a -> Bool;
eq_wrap x y = x == y;

eq_export_helper_int :: Arith.Int -> Arith.Int -> Bool;
eq_export_helper_int x y = eq_wrap x y;

}
