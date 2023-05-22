{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Timeout(isClosedAndEmpty) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified SemanticsTypes;
import qualified Arith;

isClosedAndEmpty :: SemanticsTypes.TransactionOutput -> Bool;
isClosedAndEmpty (SemanticsTypes.TransactionOutput txOut) =
  SemanticsTypes.equal_Contract (SemanticsTypes.txOutContract txOut)
    SemanticsTypes.Close &&
    null (SemanticsTypes.accounts (SemanticsTypes.txOutState txOut));
isClosedAndEmpty (SemanticsTypes.TransactionError v) = False;

}
