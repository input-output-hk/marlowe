{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Timeout(isClosedAndEmpty) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Semantics;
import qualified SemanticsTypes;
import qualified Arith;

isClosedAndEmpty :: Semantics.TransactionOutput -> Bool;
isClosedAndEmpty (Semantics.TransactionOutput txOut) =
  SemanticsTypes.equal_Contract (Semantics.txOutContract txOut)
    SemanticsTypes.Close &&
    null (SemanticsTypes.accounts (Semantics.txOutState txOut));
isClosedAndEmpty (Semantics.TransactionError v) = False;

}
