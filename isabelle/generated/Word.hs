{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Word(Word, equal_word, less_word) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;
import qualified Type_Length;

newtype Word a = Word Arith.Int;

the_int :: forall a. (Type_Length.Len a) => Word a -> Arith.Int;
the_int (Word x) = x;

equal_word :: forall a. (Type_Length.Len a) => Word a -> Word a -> Bool;
equal_word v w = Arith.equal_int (the_int v) (the_int w);

instance (Type_Length.Len a) => Eq (Word a) where {
  a == b = equal_word a b;
};

less_word :: forall a. (Type_Length.Len a) => Word a -> Word a -> Bool;
less_word a b = Arith.less_int (the_int a) (the_int b);

}
