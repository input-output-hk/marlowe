{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module MultiAssets(Assets, asset, assetValue, plus_Assets, zero_Assets) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified SemanticsTypes;
import qualified Arith;

newtype Assets = Abs_Assets (SemanticsTypes.Token -> Arith.Nat);

asset :: SemanticsTypes.Token -> Arith.Nat -> Assets;
asset xb xc =
  Abs_Assets
    (\ t -> (if SemanticsTypes.equal_Token t xb then xc else Arith.zero_nat));

rep_Assets :: Assets -> SemanticsTypes.Token -> Arith.Nat;
rep_Assets (Abs_Assets x) = x;

assetValue :: SemanticsTypes.Token -> Assets -> Arith.Nat;
assetValue xa xb = rep_Assets xb xa;

plus_Assets :: Assets -> Assets -> Assets;
plus_Assets xb xc =
  Abs_Assets (\ tok -> Arith.plus_nat (rep_Assets xb tok) (rep_Assets xc tok));

zero_Assets :: Assets;
zero_Assets = Abs_Assets (\ _ -> Arith.zero_nat);

}
