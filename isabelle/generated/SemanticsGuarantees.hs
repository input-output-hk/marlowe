{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SemanticsGuarantees() where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Serialisation;
import qualified SemanticsTypes;
import qualified Orderings;

less_eq_Party :: SemanticsTypes.Party -> SemanticsTypes.Party -> Bool;
less_eq_Party (SemanticsTypes.Address uu) (SemanticsTypes.Role uv) = True;
less_eq_Party (SemanticsTypes.Role uw) (SemanticsTypes.Address ux) = False;
less_eq_Party (SemanticsTypes.Address x) (SemanticsTypes.Address y) =
  Serialisation.less_eq_BS x y;
less_eq_Party (SemanticsTypes.Role x) (SemanticsTypes.Role y) =
  Serialisation.less_eq_BS x y;

less_eq_Partya :: SemanticsTypes.Party -> SemanticsTypes.Party -> Bool;
less_eq_Partya a b = less_eq_Party a b;

less_Party :: SemanticsTypes.Party -> SemanticsTypes.Party -> Bool;
less_Party a b = not (less_eq_Party b a);

less_Partya :: SemanticsTypes.Party -> SemanticsTypes.Party -> Bool;
less_Partya a b = less_Party a b;

instance Orderings.Ord SemanticsTypes.Party where {
  less_eq = less_eq_Partya;
  less = less_Partya;
};

instance Orderings.Preorder SemanticsTypes.Party where {
};

instance Orderings.Order SemanticsTypes.Party where {
};

instance Orderings.Linorder SemanticsTypes.Party where {
};

less_eq_Tok :: SemanticsTypes.Token -> SemanticsTypes.Token -> Bool;
less_eq_Tok (SemanticsTypes.Token a b) (SemanticsTypes.Token c d) =
  (if Serialisation.less_BS a c then True
    else (if Serialisation.less_BS c a then False
           else Serialisation.less_eq_BS b d));

less_eq_Token :: SemanticsTypes.Token -> SemanticsTypes.Token -> Bool;
less_eq_Token a b = less_eq_Tok a b;

less_Tok :: SemanticsTypes.Token -> SemanticsTypes.Token -> Bool;
less_Tok a b = not (less_eq_Tok b a);

less_Token :: SemanticsTypes.Token -> SemanticsTypes.Token -> Bool;
less_Token a b = less_Tok a b;

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

less_eq_ValId :: SemanticsTypes.ValueId -> SemanticsTypes.ValueId -> Bool;
less_eq_ValId (SemanticsTypes.ValueId a) (SemanticsTypes.ValueId b) =
  Serialisation.less_eq_BS a b;

less_eq_ValueId :: SemanticsTypes.ValueId -> SemanticsTypes.ValueId -> Bool;
less_eq_ValueId a b = less_eq_ValId a b;

less_ValId :: SemanticsTypes.ValueId -> SemanticsTypes.ValueId -> Bool;
less_ValId (SemanticsTypes.ValueId a) (SemanticsTypes.ValueId b) =
  Serialisation.less_BS a b;

less_ValueId :: SemanticsTypes.ValueId -> SemanticsTypes.ValueId -> Bool;
less_ValueId a b = less_ValId a b;

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

less_eq_ChoId :: SemanticsTypes.ChoiceId -> SemanticsTypes.ChoiceId -> Bool;
less_eq_ChoId (SemanticsTypes.ChoiceId a b) (SemanticsTypes.ChoiceId c d) =
  (if Serialisation.less_BS a c then True
    else (if Serialisation.less_BS c a then False else less_eq_Partya b d));

less_eq_ChoiceId :: SemanticsTypes.ChoiceId -> SemanticsTypes.ChoiceId -> Bool;
less_eq_ChoiceId a b = less_eq_ChoId a b;

less_ChoId :: SemanticsTypes.ChoiceId -> SemanticsTypes.ChoiceId -> Bool;
less_ChoId a b = not (less_eq_ChoId b a);

less_ChoiceId :: SemanticsTypes.ChoiceId -> SemanticsTypes.ChoiceId -> Bool;
less_ChoiceId a b = less_ChoId a b;

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

}
