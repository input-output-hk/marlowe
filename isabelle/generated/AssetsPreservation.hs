{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  AssetsPreservation(assetsInState, assetsInTransactions,
                      assetsInExternalPayments)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Semantics;
import qualified List;
import qualified SemanticsTypes;
import qualified MultiAssets;
import qualified Arith;

assetsInInput :: SemanticsTypes.Input -> MultiAssets.Assets;
assetsInInput (SemanticsTypes.IDeposit uu uv tok money) =
  MultiAssets.asset tok (Arith.nat money);
assetsInInput (SemanticsTypes.IChoice uw ux) = MultiAssets.zero_Assets;
assetsInInput SemanticsTypes.INotify = MultiAssets.zero_Assets;

addAccountAssets ::
  ((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int) ->
    MultiAssets.Assets -> MultiAssets.Assets;
addAccountAssets ((uu, t), v) b =
  MultiAssets.plus_Assets b (MultiAssets.asset t (Arith.nat v));

assetsInAccounts ::
  [((SemanticsTypes.Party, SemanticsTypes.Token), Arith.Int)] ->
    MultiAssets.Assets;
assetsInAccounts accs =
  List.foldr addAccountAssets accs MultiAssets.zero_Assets;

assetsInState :: SemanticsTypes.State_ext () -> MultiAssets.Assets;
assetsInState state = assetsInAccounts (SemanticsTypes.accounts state);

addInputAssets ::
  SemanticsTypes.Input -> MultiAssets.Assets -> MultiAssets.Assets;
addInputAssets i a = MultiAssets.plus_Assets (assetsInInput i) a;

assetsInInputs :: [SemanticsTypes.Input] -> MultiAssets.Assets;
assetsInInputs inps = List.foldr addInputAssets inps MultiAssets.zero_Assets;

assetsInTransaction :: Semantics.Transaction_ext () -> MultiAssets.Assets;
assetsInTransaction tx = assetsInInputs (Semantics.inputs tx);

addTransactionAssets ::
  Semantics.Transaction_ext () -> MultiAssets.Assets -> MultiAssets.Assets;
addTransactionAssets tx a = MultiAssets.plus_Assets (assetsInTransaction tx) a;

assetsInTransactions :: [Semantics.Transaction_ext ()] -> MultiAssets.Assets;
assetsInTransactions txs =
  List.foldr addTransactionAssets txs MultiAssets.zero_Assets;

assetsInExternalPayment :: Semantics.Payment -> MultiAssets.Assets;
assetsInExternalPayment (Semantics.Payment uu (SemanticsTypes.Party uv) tok val)
  = MultiAssets.asset tok (Arith.nat val);
assetsInExternalPayment (Semantics.Payment uw (SemanticsTypes.Account ux) uy uz)
  = MultiAssets.zero_Assets;

addExternalPaymentAssets ::
  Semantics.Payment -> MultiAssets.Assets -> MultiAssets.Assets;
addExternalPaymentAssets p a =
  MultiAssets.plus_Assets (assetsInExternalPayment p) a;

assetsInExternalPayments :: [Semantics.Payment] -> MultiAssets.Assets;
assetsInExternalPayments ps =
  List.foldr addExternalPaymentAssets ps MultiAssets.zero_Assets;

}
