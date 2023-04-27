{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module TimeRange(calculateNonAmbiguousInterval) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified OptBoundTimeInterval;
import qualified SemanticsTypes;
import qualified Arith;

gtIfNone :: Maybe Arith.Int -> Arith.Int -> Bool;
gtIfNone Nothing uu = True;
gtIfNone (Just x) y = Arith.less_int y x;

subIfSome :: Maybe Arith.Int -> Arith.Int -> Maybe Arith.Int;
subIfSome Nothing uu = Nothing;
subIfSome (Just x) y = Just (Arith.minus_int x y);

calculateNonAmbiguousInterval ::
  Maybe Arith.Int ->
    Arith.Int ->
      SemanticsTypes.Contract ->
        (OptBoundTimeInterval.BEndpoint, OptBoundTimeInterval.BEndpoint);
calculateNonAmbiguousInterval uu uv SemanticsTypes.Close =
  (OptBoundTimeInterval.Unbounded, OptBoundTimeInterval.Unbounded);
calculateNonAmbiguousInterval n t (SemanticsTypes.Pay uw ux uy uz c) =
  calculateNonAmbiguousInterval n t c;
calculateNonAmbiguousInterval n t (SemanticsTypes.If va ct cf) =
  OptBoundTimeInterval.intersectInterval (calculateNonAmbiguousInterval n t ct)
    (calculateNonAmbiguousInterval n t cf);
calculateNonAmbiguousInterval n t (SemanticsTypes.When [] timeout tcont) =
  (if Arith.less_int t timeout
    then (OptBoundTimeInterval.Unbounded,
           OptBoundTimeInterval.Bounded (Arith.minus_int timeout Arith.one_int))
    else OptBoundTimeInterval.intersectInterval
           (OptBoundTimeInterval.Bounded timeout,
             OptBoundTimeInterval.Unbounded)
           (calculateNonAmbiguousInterval n t tcont));
calculateNonAmbiguousInterval n t
  (SemanticsTypes.When (SemanticsTypes.Case vb cont : restCases) timeout tcont)
  = (if gtIfNone n Arith.zero_int
      then OptBoundTimeInterval.intersectInterval
             (calculateNonAmbiguousInterval (subIfSome n Arith.one_int) t cont)
             (calculateNonAmbiguousInterval n t
               (SemanticsTypes.When restCases timeout tcont))
      else calculateNonAmbiguousInterval n t
             (SemanticsTypes.When restCases timeout tcont));
calculateNonAmbiguousInterval n t (SemanticsTypes.Let vc vd c) =
  calculateNonAmbiguousInterval n t c;
calculateNonAmbiguousInterval n t (SemanticsTypes.Assert ve c) =
  calculateNonAmbiguousInterval n t c;

}
