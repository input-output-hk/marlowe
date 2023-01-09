{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module PositiveAccounts(validAndPositive_state) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified SemanticsGuarantees;
import qualified Product_Type;
import qualified List;
import qualified SemanticsTypes;
import qualified Arith;

allAccountsPositive ::
  [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] -> Bool;
allAccountsPositive accs =
  List.foldl
    (\ r (a, b) ->
      (case a of {
        (_, _) -> (\ money -> r && Arith.less_int Arith.zero_int money);
      })
        b)
    True accs;

allAccountsPositiveState :: SemanticsTypes.State_ext () -> Bool;
allAccountsPositiveState state =
  allAccountsPositive (SemanticsTypes.accounts state);

validAndPositive_state :: SemanticsTypes.State_ext () -> Bool;
validAndPositive_state state =
  SemanticsGuarantees.valid_state state && allAccountsPositiveState state;

}
