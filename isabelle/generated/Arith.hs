{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Arith(Int(..), integer_of_int, equal_int, less_eq_int, less_int, Nat,
         integer_of_nat, Num(..), One, Zero, Zero_neq_one, nat, plus_nat, suc,
         uminus_int, zero_int, abs_int, one_int, plus_int, zero_nat, minus_int,
         times_int, of_bool, divide_int)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified Orderings;

newtype Int = Int_of_integer Integer deriving (Prelude.Read, Prelude.Show);

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

instance Orderings.Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

newtype Nat = Nat Integer deriving (Prelude.Read, Prelude.Show);

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Orderings.Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

data Num = One | Bit0 Num | Bit1 Num deriving (Prelude.Read, Prelude.Show);

one_integer :: Integer;
one_integer = (1 :: Integer);

class One a where {
  one :: a;
};

instance One Integer where {
  one = one_integer;
};

class Zero a where {
  zero :: a;
};

instance Zero Integer where {
  zero = (0 :: Integer);
};

instance Orderings.Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

class (One a, Zero a) => Zero_neq_one a where {
};

instance Zero_neq_one Integer where {
};

nat :: Int -> Nat;
nat k = Nat (Orderings.max (0 :: Integer) (integer_of_int k));

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

abs_int :: Int -> Int;
abs_int i = (if less_int i zero_int then uminus_int i else i);

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else Product_Type.apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

of_bool :: forall a. (Zero_neq_one a) => Bool -> a;
of_bool True = one;
of_bool False = zero;

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

}
