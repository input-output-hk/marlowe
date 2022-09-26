{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Serialisation(ByteString, less_eq_BS, less_BS, equal_ByteString) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Type_Length;
import qualified Numeral_Type;
import qualified Word;

newtype ByteString = ByteString
  [Word.Word
     (Numeral_Type.Bit0
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))];

less_eq_BSa ::
  [Word.Word
     (Numeral_Type.Bit0
       (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))] ->
    [Word.Word
       (Numeral_Type.Bit0
         (Numeral_Type.Bit0 (Numeral_Type.Bit0 Numeral_Type.Num1)))] ->
      Bool;
less_eq_BSa [] [] = True;
less_eq_BSa (uu : uv) [] = False;
less_eq_BSa [] (uw : ux) = True;
less_eq_BSa (h1 : t1) (h2 : t2) =
  (if Word.less_word h2 h1 then False
    else (if Word.equal_word h1 h2 then less_eq_BSa t1 t2 else True));

less_eq_BS :: ByteString -> ByteString -> Bool;
less_eq_BS (ByteString xs) (ByteString ys) = less_eq_BSa xs ys;

less_BS :: ByteString -> ByteString -> Bool;
less_BS a b = not (less_eq_BS b a);

equal_ByteString :: ByteString -> ByteString -> Bool;
equal_ByteString (ByteString x) (ByteString ya) = x == ya;

}
