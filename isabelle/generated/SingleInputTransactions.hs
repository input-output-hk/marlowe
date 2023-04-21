{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SingleInputTransactions(traceListToSingleInput) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified SemanticsTypes;
import qualified Arith;

inputsToTransactions ::
  (Arith.Int, Arith.Int) ->
    [SemanticsTypes.Input] -> [SemanticsTypes.Transaction_ext ()];
inputsToTransactions si [] = [SemanticsTypes.Transaction_ext si [] ()];
inputsToTransactions si [inp1] = [SemanticsTypes.Transaction_ext si [inp1] ()];
inputsToTransactions si (inp1 : v : va) =
  SemanticsTypes.Transaction_ext si [inp1] () :
    inputsToTransactions si (v : va);

traceListToSingleInput ::
  [SemanticsTypes.Transaction_ext ()] -> [SemanticsTypes.Transaction_ext ()];
traceListToSingleInput [] = [];
traceListToSingleInput (SemanticsTypes.Transaction_ext si inps () : rest) =
  inputsToTransactions si inps ++ traceListToSingleInput rest;

}
