{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SingleInputTransactions(traceListToSingleInput) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Semantics;
import qualified SemanticsTypes;
import qualified Arith;

inputsToTransactions ::
  (Arith.Int, Arith.Int) ->
    [SemanticsTypes.Input] -> [Semantics.Transaction_ext ()];
inputsToTransactions si [] = [Semantics.Transaction_ext si [] ()];
inputsToTransactions si [inp1] = [Semantics.Transaction_ext si [inp1] ()];
inputsToTransactions si (inp1 : v : va) =
  Semantics.Transaction_ext si [inp1] () : inputsToTransactions si (v : va);

traceListToSingleInput ::
  [Semantics.Transaction_ext ()] -> [Semantics.Transaction_ext ()];
traceListToSingleInput [] = [];
traceListToSingleInput (Semantics.Transaction_ext si inps () : rest) =
  inputsToTransactions si inps ++ traceListToSingleInput rest;

}
