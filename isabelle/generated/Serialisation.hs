{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Serialisation(less_eq_BS, less_BS) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Type_Length;
import qualified Numeral_Type;
import qualified Word;

less_eq_BS ::
  [Word.Word
     (Numeral_Type.Bit0
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))] ->
    [Word.Word
       (Numeral_Type.Bit0
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))] ->
      Bool;
less_eq_BS [] [] = True;
less_eq_BS (uu : uv) [] = False;
less_eq_BS [] (uw : ux) = True;
less_eq_BS (h1 : t1) (h2 : t2) =
  (if Word.less_word h2 h1 then False
    else (if Word.equal_word h1 h2 then less_eq_BS t1 t2 else True));

less_BS ::
  [Word.Word
     (Numeral_Type.Bit0
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))] ->
    [Word.Word
       (Numeral_Type.Bit0
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))] ->
      Bool;
less_BS a b = not (less_eq_BS b a);

}
