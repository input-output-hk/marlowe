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
inputsToTransactions ti [] = [SemanticsTypes.Transaction_ext ti [] ()];
inputsToTransactions ti [inp1] = [SemanticsTypes.Transaction_ext ti [inp1] ()];
inputsToTransactions ti (headInput : v : va) =
  SemanticsTypes.Transaction_ext ti [headInput] () :
    inputsToTransactions ti (v : va);

traceListToSingleInput ::
  [SemanticsTypes.Transaction_ext ()] -> [SemanticsTypes.Transaction_ext ()];
traceListToSingleInput [] = [];
traceListToSingleInput (SemanticsTypes.Transaction_ext si inps () : tailTx) =
  inputsToTransactions si inps ++ traceListToSingleInput tailTx;

}
