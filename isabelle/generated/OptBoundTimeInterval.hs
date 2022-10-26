{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module OptBoundTimeInterval(BEndpoint(..), intersectInterval) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Orderings;
import qualified Arith;

data BEndpoint = Unbounded | Bounded Arith.Int
  deriving (Prelude.Read, Prelude.Show);

maxLow :: BEndpoint -> BEndpoint -> BEndpoint;
maxLow Unbounded y = y;
maxLow (Bounded v) Unbounded = Bounded v;
maxLow (Bounded x) (Bounded y) = Bounded (Orderings.max x y);

minHigh :: BEndpoint -> BEndpoint -> BEndpoint;
minHigh Unbounded y = y;
minHigh (Bounded v) Unbounded = Bounded v;
minHigh (Bounded x) (Bounded y) = Bounded (Orderings.min x y);

intersectInterval ::
  (BEndpoint, BEndpoint) -> (BEndpoint, BEndpoint) -> (BEndpoint, BEndpoint);
intersectInterval (low1, high1) (low2, high2) =
  (maxLow low1 low2, minHigh high1 high2);

}
