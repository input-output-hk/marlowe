{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SemanticsGuarantees(valid_state) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified MList;
import qualified Arith;
import qualified Product_Lexorder;
import qualified SemanticsTypes;
import qualified Orderings;

less_eq_Party :: SemanticsTypes.Party -> SemanticsTypes.Party -> Bool;
less_eq_Party (SemanticsTypes.Address uu) (SemanticsTypes.Role uv) = True;
less_eq_Party (SemanticsTypes.Role uw) (SemanticsTypes.Address ux) = False;
less_eq_Party (SemanticsTypes.Address x) (SemanticsTypes.Address y) = x <= y;
less_eq_Party (SemanticsTypes.Role x) (SemanticsTypes.Role y) = x <= y;

less_Party :: SemanticsTypes.Party -> SemanticsTypes.Party -> Bool;
less_Party a b = not (less_eq_Party b a);

instance Orderings.Ord SemanticsTypes.Party where {
  less_eq = less_eq_Party;
  less = less_Party;
};

instance Orderings.Preorder SemanticsTypes.Party where {
};

instance Orderings.Order SemanticsTypes.Party where {
};

instance Orderings.Linorder SemanticsTypes.Party where {
};

less_eq_Token :: SemanticsTypes.Token -> SemanticsTypes.Token -> Bool;
less_eq_Token (SemanticsTypes.Token currencyA tokenA)
  (SemanticsTypes.Token currencyB tokenB) =
  (if currencyA < currencyB then True
    else (if currencyB < currencyA then False else tokenA <= tokenB));

less_Token :: SemanticsTypes.Token -> SemanticsTypes.Token -> Bool;
less_Token a b = not (less_eq_Token b a);

instance Orderings.Ord SemanticsTypes.Token where {
  less_eq = less_eq_Token;
  less = less_Token;
};

instance Orderings.Preorder SemanticsTypes.Token where {
};

instance Orderings.Order SemanticsTypes.Token where {
};

instance Orderings.Linorder SemanticsTypes.Token where {
};

less_eq_ValueId :: SemanticsTypes.ValueId -> SemanticsTypes.ValueId -> Bool;
less_eq_ValueId (SemanticsTypes.ValueId a) (SemanticsTypes.ValueId b) = a <= b;

less_ValueId :: SemanticsTypes.ValueId -> SemanticsTypes.ValueId -> Bool;
less_ValueId (SemanticsTypes.ValueId a) (SemanticsTypes.ValueId b) = a < b;

instance Orderings.Ord SemanticsTypes.ValueId where {
  less_eq = less_eq_ValueId;
  less = less_ValueId;
};

instance Orderings.Preorder SemanticsTypes.ValueId where {
};

instance Orderings.Order SemanticsTypes.ValueId where {
};

instance Orderings.Linorder SemanticsTypes.ValueId where {
};

less_eq_ChoiceId :: SemanticsTypes.ChoiceId -> SemanticsTypes.ChoiceId -> Bool;
less_eq_ChoiceId (SemanticsTypes.ChoiceId nameA partyA)
  (SemanticsTypes.ChoiceId nameB partyB) =
  (if nameA < nameB then True
    else (if nameB < nameA then False else less_eq_Party partyA partyB));

less_ChoiceId :: SemanticsTypes.ChoiceId -> SemanticsTypes.ChoiceId -> Bool;
less_ChoiceId a b = not (less_eq_ChoiceId b a);

instance Orderings.Ord SemanticsTypes.ChoiceId where {
  less_eq = less_eq_ChoiceId;
  less = less_ChoiceId;
};

instance Orderings.Preorder SemanticsTypes.ChoiceId where {
};

instance Orderings.Order SemanticsTypes.ChoiceId where {
};

instance Orderings.Linorder SemanticsTypes.ChoiceId where {
};

valid_state :: SemanticsTypes.State_ext () -> Bool;
valid_state state =
  MList.valid_map (SemanticsTypes.accounts state) &&
    MList.valid_map (SemanticsTypes.choices state) &&
      MList.valid_map (SemanticsTypes.boundValues state);

}
