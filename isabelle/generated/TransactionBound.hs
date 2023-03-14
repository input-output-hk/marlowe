{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module TransactionBound(maxTransactionsInitialState) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Orderings;
import qualified SemanticsTypes;
import qualified Arith;

countWhens :: SemanticsTypes.Contract -> Arith.Nat;
countWhens SemanticsTypes.Close = Arith.zero_nat;
countWhens (SemanticsTypes.Pay uv uw ux uy c) = countWhens c;
countWhens (SemanticsTypes.If uz c c2) =
  Orderings.max (countWhens c) (countWhens c2);
countWhens (SemanticsTypes.When cl t c) =
  Arith.suc (Orderings.max (countWhensCaseList cl) (countWhens c));
countWhens (SemanticsTypes.Let va vb c) = countWhens c;
countWhens (SemanticsTypes.Assert vc c) = Arith.suc (countWhens c);

countWhensCaseList :: [SemanticsTypes.Case] -> Arith.Nat;
countWhensCaseList (SemanticsTypes.Case uu c : tail) =
  Orderings.max (countWhens c) (countWhensCaseList tail);
countWhensCaseList [] = Arith.zero_nat;

maxTransactionsInitialState :: SemanticsTypes.Contract -> Arith.Nat;
maxTransactionsInitialState (SemanticsTypes.When cl n c) =
  countWhens (SemanticsTypes.When cl n c);
maxTransactionsInitialState SemanticsTypes.Close =
  countWhens SemanticsTypes.Close;
maxTransactionsInitialState (SemanticsTypes.Pay v va vb vc vd) =
  Arith.suc (countWhens (SemanticsTypes.Pay v va vb vc vd));
maxTransactionsInitialState (SemanticsTypes.If v va vb) =
  Arith.suc (countWhens (SemanticsTypes.If v va vb));
maxTransactionsInitialState (SemanticsTypes.Let v va vb) =
  Arith.suc (countWhens (SemanticsTypes.Let v va vb));
maxTransactionsInitialState (SemanticsTypes.Assert v va) =
  Arith.suc (countWhens (SemanticsTypes.Assert v va));

}
