{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module SemanticsCoq where

import qualified Prelude
import qualified Data.List

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

data Bool =
   True
 | False
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data Option a =
   Some a
 | None
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data Prod a b =
   Pair a b
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

prod_rect :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rect f p =
  case p of {
   Pair x x0 -> f x x0}

prod_rec :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rec =
  prod_rect

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type _ _ =
  compareSpec2Type

data Sumbool =
   Left
 | Right
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

max :: Nat -> Nat -> Nat
max n m =
  case n of {
   O -> m;
   S n' -> case m of {
            O -> n;
            S m' -> S (max n' m')}}

min :: Nat -> Nat -> Nat
min n m =
  case n of {
   O -> O;
   S n' -> case m of {
            O -> O;
            S m' -> S (min n' m')}}

fix_F :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
fix_F f x =
  f x (\y _ -> fix_F f y)

fix :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
fix =
  fix_F

positive_rect :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                 a1) -> a1 -> Prelude.Integer -> a1
positive_rect f f0 f1 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> f p0 (positive_rect f f0 f1 p0))
    (\p0 -> f0 p0 (positive_rect f f0 f1 p0))
    (\_ -> f1)
    p

positive_rec :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                a1) -> a1 -> Prelude.Integer -> a1
positive_rec =
  positive_rect

z_rect :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
          Prelude.Integer -> a1
z_rect f f0 f1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> f)
    (\x -> f0 x)
    (\x -> f1 x)
    z

z_rec :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
         Prelude.Integer -> a1
z_rec =
  z_rect

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

add0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add0 x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add0 p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add0 p q))
      (\q -> (\x -> 2 Prelude.* x) (add0 p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) q)
      (\_ -> (\x -> 2 Prelude.* x) 1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add0 p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ q))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) 1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
    (\_ -> 1)
    x

compare_cont :: Comparison -> Prelude.Integer -> Prelude.Integer ->
                Comparison
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Gt p q)
      (\_ -> Gt)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont Lt p q)
      (\q -> compare_cont r p q)
      (\_ -> Gt)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Lt)
      (\_ -> Lt)
      (\_ -> r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare =
  compare_cont Eq

eqb :: Prelude.Integer -> Prelude.Integer -> Bool
eqb p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> eqb p0 q0)
      (\_ -> False)
      (\_ -> False)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> False)
      (\q0 -> eqb p0 q0)
      (\_ -> False)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> False)
      (\_ -> False)
      (\_ -> True)
      q)
    p

eq_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec x y =
  positive_rec (\_ h x0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p0))
      (\_ -> Right)
      (\_ -> Right)
      x0) (\_ h x0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Right)
      (\p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h p0))
      (\_ -> Right)
      x0) (\x0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Right)
      (\_ -> Right)
      (\_ -> Left)
      x0) x y

double :: Prelude.Integer -> Prelude.Integer
double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x) p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x) p))
    x

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double (pos_sub p q))
      (\q -> succ_double (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> pred_double0 (pos_sub p q))
      (\q -> double (pos_sub p q))
      (\_ -> (\x -> x) (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x) q))
      (\q -> Prelude.negate (pred_double q))
      (\_ -> 0)
      y)
    x

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\x0 -> Prelude.negate x0)
    (\x0 -> (\x -> x) x0)
    x

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Eq)
      (\_ -> Lt)
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Gt)
      (\y' -> compare x' y')
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Lt)
      (\_ -> Lt)
      (\y' -> compOpp (compare x' y'))
      y)
    x

leb :: Prelude.Integer -> Prelude.Integer -> Bool
leb x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb :: Prelude.Integer -> Prelude.Integer -> Bool
ltb x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

geb :: Prelude.Integer -> Prelude.Integer -> Bool
geb x y =
  case compare0 x y of {
   Lt -> False;
   _ -> True}

gtb :: Prelude.Integer -> Prelude.Integer -> Bool
gtb x y =
  case compare0 x y of {
   Gt -> True;
   _ -> False}

eqb0 :: Prelude.Integer -> Prelude.Integer -> Bool
eqb0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> True)
      (\_ -> False)
      (\_ -> False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> False)
      (\q -> eqb p q)
      (\_ -> False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> False)
      (\_ -> False)
      (\q -> eqb p q)
      y)
    x

eq_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec0 x y =
  z_rec (\x0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Left)
      (\_ -> Right)
      (\_ -> Right)
      x0) (\p x0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Right)
      (\p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (eq_dec p p0))
      (\_ -> Right)
      x0) (\p x0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Right)
      (\_ -> Right)
      (\p0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (eq_dec p p0))
      x0) x y

z_lt_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_dec x y =
  case compare0 x y of {
   Lt -> Left;
   _ -> Right}

z_le_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_le_dec x y =
  case compare0 x y of {
   Gt -> Right;
   _ -> Left}

z_lt_ge_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_ge_dec =
  z_lt_dec

z_le_gt_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_le_gt_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_le_dec x y)

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (List a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   Nil -> a0;
   Cons b t -> fold_left f t (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (List a2) -> a1
fold_right f a0 l =
  case l of {
   Nil -> a0;
   Cons b t -> f b (fold_right f a0 t)}

filter :: (a1 -> Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     True -> Cons x (filter f l0);
     False -> filter f l0}}

data Compare x =
   LT
 | EQ
 | GT
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

compare_rect :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) ->
                (Compare a1) -> a2
compare_rect _ _ f f0 f1 c =
  case c of {
   LT -> f __;
   EQ -> f0 __;
   GT -> f1 __}

compare_rec :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) -> (Compare
               a1) -> a2
compare_rec =
  compare_rect

type T = Prelude.Integer

_0 :: Prelude.Integer
_0 =
  0

_1 :: Prelude.Integer
_1 =
  (\x -> x) 1

_2 :: Prelude.Integer
_2 =
  (\x -> x) ((\x -> 2 Prelude.* x) 1)

add1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add1 =
  (Prelude.+)

max0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max0 =
  Prelude.max

ltb0 :: Prelude.Integer -> Prelude.Integer -> Bool
ltb0 =
  ltb

leb0 :: Prelude.Integer -> Prelude.Integer -> Bool
leb0 =
  leb

gt_le_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
gt_le_dec i j =
  let {b = ltb j i} in case b of {
                        True -> Left;
                        False -> Right}

ge_lt_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
ge_lt_dec i j =
  let {b = ltb i j} in case b of {
                        True -> Right;
                        False -> Left}

compareZdec :: Prelude.Integer -> Prelude.Integer -> Sumor Sumbool
compareZdec x y =
  let {h = z_lt_ge_dec x y} in
  case h of {
   Left -> Inleft Left;
   Right ->
    let {h0 = eq_dec0 x y} in
    case h0 of {
     Left -> Inleft Right;
     Right -> Inright}}

doubleInduction :: ((List a1) -> a2) -> ((List a1) -> a2) -> (a1 -> a1 ->
                   (List a1) -> (List a1) -> a2 -> a2) -> (List a1) -> (List
                   a1) -> a2
doubleInduction x0 x1 x2 n =
  list_rect x0 (\a n0 iHn m ->
    case m of {
     Nil -> x1 (Cons a n0);
     Cons t0 m0 -> x2 a t0 n0 m0 (iHn m0)}) n

type Person = Prelude.Integer

type BlockNumber = Prelude.Integer

type OST = BlockNumber
  -- singleton inductive, whose constructor was OS
  
blockNumber :: OST -> BlockNumber
blockNumber o =
  o

emptyOS :: OST
emptyOS =
  0

type Cash = Prelude.Integer

type ConcreteChoice = Prelude.Integer

type Timeout = Prelude.Integer

type IdentCCT =
  Prelude.Integer
  -- singleton inductive, whose constructor was IdentCC
  
type IdentChoiceT =
  Prelude.Integer
  -- singleton inductive, whose constructor was IdentChoice
  
type IdentPayT =
  Prelude.Integer
  -- singleton inductive, whose constructor was IdentPay
  
data CCT =
   CC IdentCCT Person Cash Timeout
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data RCT =
   RC IdentCCT Person Cash
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

type S0 = CCT

type S1 = S0

st :: S1 -> List Prelude.Integer
st cct =
  case cct of {
   CC i p c t0 -> Cons i (Cons p (Cons c (Cons t0 Nil)))}

type T0 = S1

compareList :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
               Sumbool
compareList x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec :: T0 -> T0 -> Sumor Sumbool
compareDec x y =
  compareList
    (case x of {
      CC i p c t0 -> Cons i (Cons p (Cons c (Cons t0 Nil)))})
    (case y of {
      CC i p c t0 -> Cons i (Cons p (Cons c (Cons t0 Nil)))})

compare1 :: T0 -> T0 -> Compare T0
compare1 x y =
  let {h = compareDec x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec1 :: T0 -> T0 -> Sumbool
eq_dec1 x y =
  let {h = compareDec x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type T1 = S1

eq_dec2 :: S1 -> S1 -> Sumbool
eq_dec2 =
  eq_dec1

compare2 :: S1 -> S1 -> Comparison
compare2 x y =
  case compare1 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

type Elt = S1

data Tree =
   Leaf
 | Node T Tree S1 Tree
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

empty :: Tree
empty =
  Leaf

is_empty :: Tree -> Bool
is_empty t =
  case t of {
   Leaf -> True;
   Node _ _ _ _ -> False}

mem :: S1 -> Tree -> Bool
mem x t =
  case t of {
   Leaf -> False;
   Node _ l k r ->
    case compare1 x k of {
     LT -> mem x l;
     EQ -> True;
     GT -> mem x r}}

min_elt :: Tree -> Option Elt
min_elt t =
  case t of {
   Leaf -> None;
   Node _ l x _ -> case l of {
                    Leaf -> Some x;
                    Node _ _ _ _ -> min_elt l}}

max_elt :: Tree -> Option Elt
max_elt t =
  case t of {
   Leaf -> None;
   Node _ _ x r -> case r of {
                    Leaf -> Some x;
                    Node _ _ _ _ -> max_elt r}}

choose :: Tree -> Option Elt
choose =
  min_elt

fold :: (Elt -> a1 -> a1) -> Tree -> a1 -> a1
fold f t base =
  case t of {
   Leaf -> base;
   Node _ l x r -> fold f r (f x (fold f l base))}

elements_aux :: (List S1) -> Tree -> List S1
elements_aux acc s =
  case s of {
   Leaf -> acc;
   Node _ l x r -> elements_aux (Cons x (elements_aux acc r)) l}

elements :: Tree -> List S1
elements =
  elements_aux Nil

rev_elements_aux :: (List S1) -> Tree -> List S1
rev_elements_aux acc s =
  case s of {
   Leaf -> acc;
   Node _ l x r -> rev_elements_aux (Cons x (rev_elements_aux acc l)) r}

rev_elements :: Tree -> List S1
rev_elements =
  rev_elements_aux Nil

cardinal :: Tree -> Nat
cardinal s =
  case s of {
   Leaf -> O;
   Node _ l _ r -> S (add (cardinal l) (cardinal r))}

maxdepth :: Tree -> Nat
maxdepth s =
  case s of {
   Leaf -> O;
   Node _ l _ r -> S (max (maxdepth l) (maxdepth r))}

mindepth :: Tree -> Nat
mindepth s =
  case s of {
   Leaf -> O;
   Node _ l _ r -> S (min (mindepth l) (mindepth r))}

for_all :: (Elt -> Bool) -> Tree -> Bool
for_all f s =
  case s of {
   Leaf -> True;
   Node _ l x r ->
    case case f x of {
          True -> for_all f l;
          False -> False} of {
     True -> for_all f r;
     False -> False}}

exists_ :: (Elt -> Bool) -> Tree -> Bool
exists_ f s =
  case s of {
   Leaf -> False;
   Node _ l x r ->
    case case f x of {
          True -> True;
          False -> exists_ f l} of {
     True -> True;
     False -> exists_ f r}}

data Enumeration =
   End
 | More Elt Tree Enumeration
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

cons :: Tree -> Enumeration -> Enumeration
cons s e =
  case s of {
   Leaf -> e;
   Node _ l x r -> cons l (More x r e)}

compare_more :: S1 -> (Enumeration -> Comparison) -> Enumeration ->
                Comparison
compare_more x1 cont e2 =
  case e2 of {
   End -> Gt;
   More x2 r2 e3 ->
    case compare1 x1 x2 of {
     LT -> Lt;
     EQ -> cont (cons r2 e3);
     GT -> Gt}}

compare_cont0 :: Tree -> (Enumeration -> Comparison) -> Enumeration ->
                 Comparison
compare_cont0 s1 cont e2 =
  case s1 of {
   Leaf -> cont e2;
   Node _ l1 x1 r1 ->
    compare_cont0 l1 (compare_more x1 (compare_cont0 r1 cont)) e2}

compare_end :: Enumeration -> Comparison
compare_end e2 =
  case e2 of {
   End -> Eq;
   More _ _ _ -> Lt}

compare3 :: Tree -> Tree -> Comparison
compare3 s1 s2 =
  compare_cont0 s1 compare_end (cons s2 End)

equal :: Tree -> Tree -> Bool
equal s1 s2 =
  case compare3 s1 s2 of {
   Eq -> True;
   _ -> False}

subsetl :: (Tree -> Bool) -> S1 -> Tree -> Bool
subsetl subset_l1 x1 s2 =
  case s2 of {
   Leaf -> False;
   Node _ l2 x2 r2 ->
    case compare1 x1 x2 of {
     LT -> subsetl subset_l1 x1 l2;
     EQ -> subset_l1 l2;
     GT -> case mem x1 r2 of {
            True -> subset_l1 s2;
            False -> False}}}

subsetr :: (Tree -> Bool) -> S1 -> Tree -> Bool
subsetr subset_r1 x1 s2 =
  case s2 of {
   Leaf -> False;
   Node _ l2 x2 r2 ->
    case compare1 x1 x2 of {
     LT -> case mem x1 l2 of {
            True -> subset_r1 s2;
            False -> False};
     EQ -> subset_r1 r2;
     GT -> subsetr subset_r1 x1 r2}}

subset :: Tree -> Tree -> Bool
subset s1 s2 =
  case s1 of {
   Leaf -> True;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> False;
     Node _ l2 x2 r2 ->
      case compare1 x1 x2 of {
       LT ->
        case subsetl (subset l1) x1 l2 of {
         True -> subset r1 s2;
         False -> False};
       EQ -> case subset l1 l2 of {
              True -> subset r1 r2;
              False -> False};
       GT ->
        case subsetr (subset r1) x1 r2 of {
         True -> subset l1 s2;
         False -> False}}}}

type T2 = Tree

height :: T2 -> T
height s =
  case s of {
   Leaf -> _0;
   Node h _ _ _ -> h}

singleton :: S1 -> Tree
singleton x =
  Node _1 Leaf x Leaf

create :: T2 -> S1 -> T2 -> Tree
create l x r =
  Node (add1 (max0 (height l) (height r)) _1) l x r

assert_false :: T2 -> S1 -> T2 -> Tree
assert_false =
  create

bal :: T2 -> S1 -> T2 -> Tree
bal l x r =
  let {hl = height l} in
  let {hr = height r} in
  case ltb0 (add1 hr _2) hl of {
   True ->
    case l of {
     Leaf -> assert_false l x r;
     Node _ ll lx lr ->
      case leb0 (height lr) (height ll) of {
       True -> create ll lx (create lr x r);
       False ->
        case lr of {
         Leaf -> assert_false l x r;
         Node _ lrl lrx lrr -> create (create ll lx lrl) lrx (create lrr x r)}}};
   False ->
    case ltb0 (add1 hl _2) hr of {
     True ->
      case r of {
       Leaf -> assert_false l x r;
       Node _ rl rx rr ->
        case leb0 (height rl) (height rr) of {
         True -> create (create l x rl) rx rr;
         False ->
          case rl of {
           Leaf -> assert_false l x r;
           Node _ rll rlx rlr ->
            create (create l x rll) rlx (create rlr rx rr)}}};
     False -> create l x r}}

add2 :: S1 -> Tree -> Tree
add2 x s =
  case s of {
   Leaf -> Node _1 Leaf x Leaf;
   Node h l y r ->
    case compare1 x y of {
     LT -> bal (add2 x l) y r;
     EQ -> Node h l y r;
     GT -> bal l y (add2 x r)}}

join :: Tree -> Elt -> T2 -> T2
join l =
  case l of {
   Leaf -> add2;
   Node lh ll lx lr -> (\x ->
    let {
     join_aux r =
       case r of {
        Leaf -> add2 x l;
        Node rh rl rx rr ->
         case ltb0 (add1 rh _2) lh of {
          True -> bal ll lx (join lr x r);
          False ->
           case ltb0 (add1 lh _2) rh of {
            True -> bal (join_aux rl) rx rr;
            False -> create l x r}}}}
    in join_aux)}

remove_min :: Tree -> Elt -> T2 -> Prod T2 Elt
remove_min l x r =
  case l of {
   Leaf -> Pair r x;
   Node _ ll lx lr ->
    case remove_min ll lx lr of {
     Pair l' m -> Pair (bal l' x r) m}}

merge :: Tree -> Tree -> Tree
merge s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node _ l2 x2 r2 ->
      case remove_min l2 x2 r2 of {
       Pair s2' m -> bal s1 m s2'}}}

remove :: S1 -> Tree -> Tree
remove x s =
  case s of {
   Leaf -> Leaf;
   Node _ l y r ->
    case compare1 x y of {
     LT -> bal (remove x l) y r;
     EQ -> merge l r;
     GT -> bal l y (remove x r)}}

concat :: Tree -> Tree -> Tree
concat s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node _ _ _ _ ->
    case s2 of {
     Leaf -> s1;
     Node _ l2 x2 r2 ->
      case remove_min l2 x2 r2 of {
       Pair s2' m -> join s1 m s2'}}}

data Triple =
   Mktriple T2 Bool T2
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

t_left :: Triple -> T2
t_left t =
  case t of {
   Mktriple t_left5 _ _ -> t_left5}

t_in :: Triple -> Bool
t_in t =
  case t of {
   Mktriple _ t_in1 _ -> t_in1}

t_right :: Triple -> T2
t_right t =
  case t of {
   Mktriple _ _ t_right5 -> t_right5}

split :: S1 -> Tree -> Triple
split x s =
  case s of {
   Leaf -> Mktriple Leaf False Leaf;
   Node _ l y r ->
    case compare1 x y of {
     LT ->
      case split x l of {
       Mktriple ll b rl -> Mktriple ll b (join rl y r)};
     EQ -> Mktriple l True r;
     GT ->
      case split x r of {
       Mktriple rl b rr -> Mktriple (join l y rl) b rr}}}

inter :: Tree -> Tree -> Tree
inter s1 s2 =
  case s1 of {
   Leaf -> Leaf;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> Leaf;
     Node _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' pres r2' ->
        case pres of {
         True -> join (inter l1 l2') x1 (inter r1 r2');
         False -> concat (inter l1 l2') (inter r1 r2')}}}}

diff :: Tree -> Tree -> Tree
diff s1 s2 =
  case s1 of {
   Leaf -> Leaf;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> s1;
     Node _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' pres r2' ->
        case pres of {
         True -> concat (diff l1 l2') (diff r1 r2');
         False -> join (diff l1 l2') x1 (diff r1 r2')}}}}

union :: Tree -> Tree -> Tree
union s1 s2 =
  case s1 of {
   Leaf -> s2;
   Node _ l1 x1 r1 ->
    case s2 of {
     Leaf -> s1;
     Node _ _ _ _ ->
      case split x1 s2 of {
       Mktriple l2' _ r2' -> join (union l1 l2') x1 (union r1 r2')}}}

filter0 :: (Elt -> Bool) -> Tree -> Tree
filter0 f s =
  case s of {
   Leaf -> Leaf;
   Node _ l x r ->
    let {l' = filter0 f l} in
    let {r' = filter0 f r} in
    case f x of {
     True -> join l' x r';
     False -> concat l' r'}}

partition :: (Elt -> Bool) -> T2 -> Prod T2 T2
partition f s =
  case s of {
   Leaf -> Pair Leaf Leaf;
   Node _ l x r ->
    case partition f l of {
     Pair l1 l2 ->
      case partition f r of {
       Pair r1 r2 ->
        case f x of {
         True -> Pair (join l1 x r1) (concat l2 r2);
         False -> Pair (concat l1 r1) (join l2 x r2)}}}}

ltb_tree :: S1 -> Tree -> Bool
ltb_tree x s =
  case s of {
   Leaf -> True;
   Node _ l y r ->
    case compare1 x y of {
     GT -> andb (ltb_tree x l) (ltb_tree x r);
     _ -> False}}

gtb_tree :: S1 -> Tree -> Bool
gtb_tree x s =
  case s of {
   Leaf -> True;
   Node _ l y r ->
    case compare1 x y of {
     LT -> andb (gtb_tree x l) (gtb_tree x r);
     _ -> False}}

isok :: Tree -> Bool
isok s =
  case s of {
   Leaf -> True;
   Node _ l x r ->
    andb (andb (andb (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)}

type T3 = S1

compare4 :: S1 -> S1 -> Comparison
compare4 x y =
  case compare1 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec3 :: S1 -> S1 -> Sumbool
eq_dec3 =
  eq_dec2

type T4 = S1

compare5 :: S1 -> S1 -> Comparison
compare5 x y =
  case compare1 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec4 :: S1 -> S1 -> Sumbool
eq_dec4 =
  eq_dec3

eq_dec5 :: S1 -> S1 -> Sumbool
eq_dec5 =
  eq_dec2

lt_dec :: S1 -> S1 -> Sumbool
lt_dec x y =
  let {
   c = compSpec2Type x y
         (case compare1 x y of {
           LT -> Lt;
           EQ -> Eq;
           GT -> Gt})}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb1 :: S1 -> S1 -> Bool
eqb1 x y =
  case eq_dec5 x y of {
   Left -> True;
   Right -> False}

data R_min_elt =
   R_min_elt_0 Tree
 | R_min_elt_1 Tree T Tree S1 Tree
 | R_min_elt_2 Tree T Tree S1 Tree T Tree S1 Tree (Option Elt) R_min_elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_max_elt =
   R_max_elt_0 Tree
 | R_max_elt_1 Tree T Tree S1 Tree
 | R_max_elt_2 Tree T Tree S1 Tree T Tree S1 Tree (Option Elt) R_max_elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

type T5 = S1

compare6 :: S1 -> S1 -> Comparison
compare6 x y =
  case compare1 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec6 :: S1 -> S1 -> Sumbool
eq_dec6 =
  eq_dec2

type T6 = S1

compare7 :: S1 -> S1 -> Comparison
compare7 x y =
  case compare1 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec7 :: S1 -> S1 -> Sumbool
eq_dec7 =
  eq_dec6

eq_dec8 :: S1 -> S1 -> Sumbool
eq_dec8 =
  eq_dec2

lt_dec0 :: S1 -> S1 -> Sumbool
lt_dec0 x y =
  let {
   c = compSpec2Type x y
         (case compare1 x y of {
           LT -> Lt;
           EQ -> Eq;
           GT -> Gt})}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb2 :: S1 -> S1 -> Bool
eqb2 x y =
  case eq_dec8 x y of {
   Left -> True;
   Right -> False}

flatten_e :: Enumeration -> List Elt
flatten_e e =
  case e of {
   End -> Nil;
   More x t r -> Cons x (app (elements t) (flatten_e r))}

data R_bal =
   R_bal_0 T2 S1 T2
 | R_bal_1 T2 S1 T2 T Tree S1 Tree
 | R_bal_2 T2 S1 T2 T Tree S1 Tree
 | R_bal_3 T2 S1 T2 T Tree S1 Tree T Tree S1 Tree
 | R_bal_4 T2 S1 T2
 | R_bal_5 T2 S1 T2 T Tree S1 Tree
 | R_bal_6 T2 S1 T2 T Tree S1 Tree
 | R_bal_7 T2 S1 T2 T Tree S1 Tree T Tree S1 Tree
 | R_bal_8 T2 S1 T2
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_remove_min =
   R_remove_min_0 Tree Elt T2
 | R_remove_min_1 Tree Elt T2 T Tree S1 Tree (Prod T2 Elt) R_remove_min 
 T2 Elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_merge =
   R_merge_0 Tree Tree
 | R_merge_1 Tree Tree T Tree S1 Tree
 | R_merge_2 Tree Tree T Tree S1 Tree T Tree S1 Tree T2 Elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_concat =
   R_concat_0 Tree Tree
 | R_concat_1 Tree Tree T Tree S1 Tree
 | R_concat_2 Tree Tree T Tree S1 Tree T Tree S1 Tree T2 Elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_inter =
   R_inter_0 Tree Tree
 | R_inter_1 Tree Tree T Tree S1 Tree
 | R_inter_2 Tree Tree T Tree S1 Tree T Tree S1 Tree T2 Bool T2 Tree 
 R_inter Tree R_inter
 | R_inter_3 Tree Tree T Tree S1 Tree T Tree S1 Tree T2 Bool T2 Tree 
 R_inter Tree R_inter
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_diff =
   R_diff_0 Tree Tree
 | R_diff_1 Tree Tree T Tree S1 Tree
 | R_diff_2 Tree Tree T Tree S1 Tree T Tree S1 Tree T2 Bool T2 Tree R_diff 
 Tree R_diff
 | R_diff_3 Tree Tree T Tree S1 Tree T Tree S1 Tree T2 Bool T2 Tree R_diff 
 Tree R_diff
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_union =
   R_union_0 Tree Tree
 | R_union_1 Tree Tree T Tree S1 Tree
 | R_union_2 Tree Tree T Tree S1 Tree T Tree S1 Tree T2 Bool T2 Tree 
 R_union Tree R_union
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

type T7 = S1

compare8 :: S1 -> S1 -> Comparison
compare8 x y =
  case compare1 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec9 :: S1 -> S1 -> Sumbool
eq_dec9 =
  eq_dec2

type Elt0 = S1

type T_ = T2
  -- singleton inductive, whose constructor was Mkt
  
this :: T_ -> T2
this t =
  t

type T8 = T_

mem0 :: Elt0 -> T8 -> Bool
mem0 x s =
  mem x (this s)

add3 :: Elt0 -> T8 -> T8
add3 x s =
  add2 x (this s)

remove0 :: Elt0 -> T8 -> T8
remove0 x s =
  remove x (this s)

singleton0 :: Elt0 -> T8
singleton0 =
  singleton

union0 :: T8 -> T8 -> T8
union0 s s' =
  union (this s) (this s')

inter0 :: T8 -> T8 -> T8
inter0 s s' =
  inter (this s) (this s')

diff0 :: T8 -> T8 -> T8
diff0 s s' =
  diff (this s) (this s')

equal0 :: T8 -> T8 -> Bool
equal0 s s' =
  equal (this s) (this s')

subset0 :: T8 -> T8 -> Bool
subset0 s s' =
  subset (this s) (this s')

empty0 :: T8
empty0 =
  empty

is_empty0 :: T8 -> Bool
is_empty0 s =
  is_empty (this s)

elements0 :: T8 -> List Elt0
elements0 s =
  elements (this s)

choose0 :: T8 -> Option Elt0
choose0 s =
  choose (this s)

fold0 :: (Elt0 -> a1 -> a1) -> T8 -> a1 -> a1
fold0 f s =
  fold f (this s)

cardinal0 :: T8 -> Nat
cardinal0 s =
  cardinal (this s)

filter1 :: (Elt0 -> Bool) -> T8 -> T8
filter1 f s =
  filter0 f (this s)

for_all0 :: (Elt0 -> Bool) -> T8 -> Bool
for_all0 f s =
  for_all f (this s)

exists_0 :: (Elt0 -> Bool) -> T8 -> Bool
exists_0 f s =
  exists_ f (this s)

partition0 :: (Elt0 -> Bool) -> T8 -> Prod T8 T8
partition0 f s =
  let {p = partition f (this s)} in Pair (fst p) (snd p)

eq_dec10 :: T8 -> T8 -> Sumbool
eq_dec10 s0 s'0 =
  let {b = equal s0 s'0} in case b of {
                             True -> Left;
                             False -> Right}

compare9 :: T8 -> T8 -> Comparison
compare9 s s' =
  compare3 (this s) (this s')

min_elt0 :: T8 -> Option Elt0
min_elt0 s =
  min_elt (this s)

max_elt0 :: T8 -> Option Elt0
max_elt0 s =
  max_elt (this s)

type Elt1 = S1

type T9 = T8

empty1 :: T9
empty1 =
  empty0

is_empty1 :: T9 -> Bool
is_empty1 =
  is_empty0

mem1 :: Elt1 -> T9 -> Bool
mem1 =
  mem0

add4 :: Elt1 -> T9 -> T9
add4 =
  add3

singleton1 :: Elt1 -> T9
singleton1 =
  singleton0

remove1 :: Elt1 -> T9 -> T9
remove1 =
  remove0

union1 :: T9 -> T9 -> T9
union1 =
  union0

inter1 :: T9 -> T9 -> T9
inter1 =
  inter0

diff1 :: T9 -> T9 -> T9
diff1 =
  diff0

eq_dec11 :: T9 -> T9 -> Sumbool
eq_dec11 =
  eq_dec10

equal1 :: T9 -> T9 -> Bool
equal1 =
  equal0

subset1 :: T9 -> T9 -> Bool
subset1 =
  subset0

fold1 :: (Elt1 -> a1 -> a1) -> T9 -> a1 -> a1
fold1 =
  fold0

for_all1 :: (Elt1 -> Bool) -> T9 -> Bool
for_all1 =
  for_all0

exists_1 :: (Elt1 -> Bool) -> T9 -> Bool
exists_1 =
  exists_0

filter2 :: (Elt1 -> Bool) -> T9 -> T9
filter2 =
  filter1

partition1 :: (Elt1 -> Bool) -> T9 -> Prod T9 T9
partition1 =
  partition0

cardinal1 :: T9 -> Nat
cardinal1 =
  cardinal0

elements1 :: T9 -> List Elt1
elements1 =
  elements0

choose1 :: T9 -> Option Elt1
choose1 =
  choose0

eqb3 :: S1 -> S1 -> Bool
eqb3 x y =
  case eq_dec9 x y of {
   Left -> True;
   Right -> False}

min_elt1 :: T9 -> Option Elt1
min_elt1 =
  min_elt0

max_elt1 :: T9 -> Option Elt1
max_elt1 =
  max_elt0

compare10 :: T9 -> T9 -> Compare T9
compare10 s s' =
  let {c = compSpec2Type s s' (compare9 s s')} in
  case c of {
   CompEqT -> EQ;
   CompLtT -> LT;
   CompGtT -> GT}

type T10 = S1

compare11 :: S1 -> S1 -> Compare S1
compare11 =
  compare1

eq_dec12 :: S1 -> S1 -> Sumbool
eq_dec12 =
  eq_dec1

emptyCCSet :: T9
emptyCCSet =
  empty1

type S2 = RCT

type S3 = S2

st0 :: S3 -> List Prelude.Integer
st0 rct =
  case rct of {
   RC i p c -> Cons i (Cons p (Cons c Nil))}

type T11 = S3

compareList0 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList0 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec0 :: T11 -> T11 -> Sumor Sumbool
compareDec0 x y =
  compareList0 (case x of {
                 RC i p c -> Cons i (Cons p (Cons c Nil))})
    (case y of {
      RC i p c -> Cons i (Cons p (Cons c Nil))})

compare12 :: T11 -> T11 -> Compare T11
compare12 x y =
  let {h = compareDec0 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec13 :: T11 -> T11 -> Sumbool
eq_dec13 x y =
  let {h = compareDec0 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type T12 = S3

eq_dec14 :: S3 -> S3 -> Sumbool
eq_dec14 =
  eq_dec13

compare13 :: S3 -> S3 -> Comparison
compare13 x y =
  case compare12 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

type Elt2 = S3

data Tree0 =
   Leaf0
 | Node0 T Tree0 S3 Tree0
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

empty2 :: Tree0
empty2 =
  Leaf0

is_empty2 :: Tree0 -> Bool
is_empty2 t =
  case t of {
   Leaf0 -> True;
   Node0 _ _ _ _ -> False}

mem2 :: S3 -> Tree0 -> Bool
mem2 x t =
  case t of {
   Leaf0 -> False;
   Node0 _ l k r ->
    case compare12 x k of {
     LT -> mem2 x l;
     EQ -> True;
     GT -> mem2 x r}}

min_elt2 :: Tree0 -> Option Elt2
min_elt2 t =
  case t of {
   Leaf0 -> None;
   Node0 _ l x _ -> case l of {
                     Leaf0 -> Some x;
                     Node0 _ _ _ _ -> min_elt2 l}}

max_elt2 :: Tree0 -> Option Elt2
max_elt2 t =
  case t of {
   Leaf0 -> None;
   Node0 _ _ x r -> case r of {
                     Leaf0 -> Some x;
                     Node0 _ _ _ _ -> max_elt2 r}}

choose2 :: Tree0 -> Option Elt2
choose2 =
  min_elt2

fold2 :: (Elt2 -> a1 -> a1) -> Tree0 -> a1 -> a1
fold2 f t base =
  case t of {
   Leaf0 -> base;
   Node0 _ l x r -> fold2 f r (f x (fold2 f l base))}

elements_aux0 :: (List S3) -> Tree0 -> List S3
elements_aux0 acc s =
  case s of {
   Leaf0 -> acc;
   Node0 _ l x r -> elements_aux0 (Cons x (elements_aux0 acc r)) l}

elements2 :: Tree0 -> List S3
elements2 =
  elements_aux0 Nil

rev_elements_aux0 :: (List S3) -> Tree0 -> List S3
rev_elements_aux0 acc s =
  case s of {
   Leaf0 -> acc;
   Node0 _ l x r -> rev_elements_aux0 (Cons x (rev_elements_aux0 acc l)) r}

rev_elements0 :: Tree0 -> List S3
rev_elements0 =
  rev_elements_aux0 Nil

cardinal2 :: Tree0 -> Nat
cardinal2 s =
  case s of {
   Leaf0 -> O;
   Node0 _ l _ r -> S (add (cardinal2 l) (cardinal2 r))}

maxdepth0 :: Tree0 -> Nat
maxdepth0 s =
  case s of {
   Leaf0 -> O;
   Node0 _ l _ r -> S (max (maxdepth0 l) (maxdepth0 r))}

mindepth0 :: Tree0 -> Nat
mindepth0 s =
  case s of {
   Leaf0 -> O;
   Node0 _ l _ r -> S (min (mindepth0 l) (mindepth0 r))}

for_all2 :: (Elt2 -> Bool) -> Tree0 -> Bool
for_all2 f s =
  case s of {
   Leaf0 -> True;
   Node0 _ l x r ->
    case case f x of {
          True -> for_all2 f l;
          False -> False} of {
     True -> for_all2 f r;
     False -> False}}

exists_2 :: (Elt2 -> Bool) -> Tree0 -> Bool
exists_2 f s =
  case s of {
   Leaf0 -> False;
   Node0 _ l x r ->
    case case f x of {
          True -> True;
          False -> exists_2 f l} of {
     True -> True;
     False -> exists_2 f r}}

data Enumeration0 =
   End0
 | More0 Elt2 Tree0 Enumeration0
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

cons0 :: Tree0 -> Enumeration0 -> Enumeration0
cons0 s e =
  case s of {
   Leaf0 -> e;
   Node0 _ l x r -> cons0 l (More0 x r e)}

compare_more0 :: S3 -> (Enumeration0 -> Comparison) -> Enumeration0 ->
                 Comparison
compare_more0 x1 cont e2 =
  case e2 of {
   End0 -> Gt;
   More0 x2 r2 e3 ->
    case compare12 x1 x2 of {
     LT -> Lt;
     EQ -> cont (cons0 r2 e3);
     GT -> Gt}}

compare_cont1 :: Tree0 -> (Enumeration0 -> Comparison) -> Enumeration0 ->
                 Comparison
compare_cont1 s1 cont e2 =
  case s1 of {
   Leaf0 -> cont e2;
   Node0 _ l1 x1 r1 ->
    compare_cont1 l1 (compare_more0 x1 (compare_cont1 r1 cont)) e2}

compare_end0 :: Enumeration0 -> Comparison
compare_end0 e2 =
  case e2 of {
   End0 -> Eq;
   More0 _ _ _ -> Lt}

compare14 :: Tree0 -> Tree0 -> Comparison
compare14 s1 s2 =
  compare_cont1 s1 compare_end0 (cons0 s2 End0)

equal2 :: Tree0 -> Tree0 -> Bool
equal2 s1 s2 =
  case compare14 s1 s2 of {
   Eq -> True;
   _ -> False}

subsetl0 :: (Tree0 -> Bool) -> S3 -> Tree0 -> Bool
subsetl0 subset_l1 x1 s2 =
  case s2 of {
   Leaf0 -> False;
   Node0 _ l2 x2 r2 ->
    case compare12 x1 x2 of {
     LT -> subsetl0 subset_l1 x1 l2;
     EQ -> subset_l1 l2;
     GT -> case mem2 x1 r2 of {
            True -> subset_l1 s2;
            False -> False}}}

subsetr0 :: (Tree0 -> Bool) -> S3 -> Tree0 -> Bool
subsetr0 subset_r1 x1 s2 =
  case s2 of {
   Leaf0 -> False;
   Node0 _ l2 x2 r2 ->
    case compare12 x1 x2 of {
     LT -> case mem2 x1 l2 of {
            True -> subset_r1 s2;
            False -> False};
     EQ -> subset_r1 r2;
     GT -> subsetr0 subset_r1 x1 r2}}

subset2 :: Tree0 -> Tree0 -> Bool
subset2 s1 s2 =
  case s1 of {
   Leaf0 -> True;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> False;
     Node0 _ l2 x2 r2 ->
      case compare12 x1 x2 of {
       LT ->
        case subsetl0 (subset2 l1) x1 l2 of {
         True -> subset2 r1 s2;
         False -> False};
       EQ -> case subset2 l1 l2 of {
              True -> subset2 r1 r2;
              False -> False};
       GT ->
        case subsetr0 (subset2 r1) x1 r2 of {
         True -> subset2 l1 s2;
         False -> False}}}}

type T13 = Tree0

height0 :: T13 -> T
height0 s =
  case s of {
   Leaf0 -> _0;
   Node0 h _ _ _ -> h}

singleton2 :: S3 -> Tree0
singleton2 x =
  Node0 _1 Leaf0 x Leaf0

create0 :: T13 -> S3 -> T13 -> Tree0
create0 l x r =
  Node0 (add1 (max0 (height0 l) (height0 r)) _1) l x r

assert_false0 :: T13 -> S3 -> T13 -> Tree0
assert_false0 =
  create0

bal0 :: T13 -> S3 -> T13 -> Tree0
bal0 l x r =
  let {hl = height0 l} in
  let {hr = height0 r} in
  case ltb0 (add1 hr _2) hl of {
   True ->
    case l of {
     Leaf0 -> assert_false0 l x r;
     Node0 _ ll lx lr ->
      case leb0 (height0 lr) (height0 ll) of {
       True -> create0 ll lx (create0 lr x r);
       False ->
        case lr of {
         Leaf0 -> assert_false0 l x r;
         Node0 _ lrl lrx lrr ->
          create0 (create0 ll lx lrl) lrx (create0 lrr x r)}}};
   False ->
    case ltb0 (add1 hl _2) hr of {
     True ->
      case r of {
       Leaf0 -> assert_false0 l x r;
       Node0 _ rl rx rr ->
        case leb0 (height0 rl) (height0 rr) of {
         True -> create0 (create0 l x rl) rx rr;
         False ->
          case rl of {
           Leaf0 -> assert_false0 l x r;
           Node0 _ rll rlx rlr ->
            create0 (create0 l x rll) rlx (create0 rlr rx rr)}}};
     False -> create0 l x r}}

add5 :: S3 -> Tree0 -> Tree0
add5 x s =
  case s of {
   Leaf0 -> Node0 _1 Leaf0 x Leaf0;
   Node0 h l y r ->
    case compare12 x y of {
     LT -> bal0 (add5 x l) y r;
     EQ -> Node0 h l y r;
     GT -> bal0 l y (add5 x r)}}

join0 :: Tree0 -> Elt2 -> T13 -> T13
join0 l =
  case l of {
   Leaf0 -> add5;
   Node0 lh ll lx lr -> (\x ->
    let {
     join_aux r =
       case r of {
        Leaf0 -> add5 x l;
        Node0 rh rl rx rr ->
         case ltb0 (add1 rh _2) lh of {
          True -> bal0 ll lx (join0 lr x r);
          False ->
           case ltb0 (add1 lh _2) rh of {
            True -> bal0 (join_aux rl) rx rr;
            False -> create0 l x r}}}}
    in join_aux)}

remove_min0 :: Tree0 -> Elt2 -> T13 -> Prod T13 Elt2
remove_min0 l x r =
  case l of {
   Leaf0 -> Pair r x;
   Node0 _ ll lx lr ->
    case remove_min0 ll lx lr of {
     Pair l' m -> Pair (bal0 l' x r) m}}

merge0 :: Tree0 -> Tree0 -> Tree0
merge0 s1 s2 =
  case s1 of {
   Leaf0 -> s2;
   Node0 _ _ _ _ ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ l2 x2 r2 ->
      case remove_min0 l2 x2 r2 of {
       Pair s2' m -> bal0 s1 m s2'}}}

remove2 :: S3 -> Tree0 -> Tree0
remove2 x s =
  case s of {
   Leaf0 -> Leaf0;
   Node0 _ l y r ->
    case compare12 x y of {
     LT -> bal0 (remove2 x l) y r;
     EQ -> merge0 l r;
     GT -> bal0 l y (remove2 x r)}}

concat0 :: Tree0 -> Tree0 -> Tree0
concat0 s1 s2 =
  case s1 of {
   Leaf0 -> s2;
   Node0 _ _ _ _ ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ l2 x2 r2 ->
      case remove_min0 l2 x2 r2 of {
       Pair s2' m -> join0 s1 m s2'}}}

data Triple0 =
   Mktriple0 T13 Bool T13
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

t_left0 :: Triple0 -> T13
t_left0 t =
  case t of {
   Mktriple0 t_left5 _ _ -> t_left5}

t_in0 :: Triple0 -> Bool
t_in0 t =
  case t of {
   Mktriple0 _ t_in1 _ -> t_in1}

t_right0 :: Triple0 -> T13
t_right0 t =
  case t of {
   Mktriple0 _ _ t_right5 -> t_right5}

split0 :: S3 -> Tree0 -> Triple0
split0 x s =
  case s of {
   Leaf0 -> Mktriple0 Leaf0 False Leaf0;
   Node0 _ l y r ->
    case compare12 x y of {
     LT ->
      case split0 x l of {
       Mktriple0 ll b rl -> Mktriple0 ll b (join0 rl y r)};
     EQ -> Mktriple0 l True r;
     GT ->
      case split0 x r of {
       Mktriple0 rl b rr -> Mktriple0 (join0 l y rl) b rr}}}

inter2 :: Tree0 -> Tree0 -> Tree0
inter2 s1 s2 =
  case s1 of {
   Leaf0 -> Leaf0;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> Leaf0;
     Node0 _ _ _ _ ->
      case split0 x1 s2 of {
       Mktriple0 l2' pres r2' ->
        case pres of {
         True -> join0 (inter2 l1 l2') x1 (inter2 r1 r2');
         False -> concat0 (inter2 l1 l2') (inter2 r1 r2')}}}}

diff2 :: Tree0 -> Tree0 -> Tree0
diff2 s1 s2 =
  case s1 of {
   Leaf0 -> Leaf0;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ _ _ _ ->
      case split0 x1 s2 of {
       Mktriple0 l2' pres r2' ->
        case pres of {
         True -> concat0 (diff2 l1 l2') (diff2 r1 r2');
         False -> join0 (diff2 l1 l2') x1 (diff2 r1 r2')}}}}

union2 :: Tree0 -> Tree0 -> Tree0
union2 s1 s2 =
  case s1 of {
   Leaf0 -> s2;
   Node0 _ l1 x1 r1 ->
    case s2 of {
     Leaf0 -> s1;
     Node0 _ _ _ _ ->
      case split0 x1 s2 of {
       Mktriple0 l2' _ r2' -> join0 (union2 l1 l2') x1 (union2 r1 r2')}}}

filter3 :: (Elt2 -> Bool) -> Tree0 -> Tree0
filter3 f s =
  case s of {
   Leaf0 -> Leaf0;
   Node0 _ l x r ->
    let {l' = filter3 f l} in
    let {r' = filter3 f r} in
    case f x of {
     True -> join0 l' x r';
     False -> concat0 l' r'}}

partition2 :: (Elt2 -> Bool) -> T13 -> Prod T13 T13
partition2 f s =
  case s of {
   Leaf0 -> Pair Leaf0 Leaf0;
   Node0 _ l x r ->
    case partition2 f l of {
     Pair l1 l2 ->
      case partition2 f r of {
       Pair r1 r2 ->
        case f x of {
         True -> Pair (join0 l1 x r1) (concat0 l2 r2);
         False -> Pair (concat0 l1 r1) (join0 l2 x r2)}}}}

ltb_tree0 :: S3 -> Tree0 -> Bool
ltb_tree0 x s =
  case s of {
   Leaf0 -> True;
   Node0 _ l y r ->
    case compare12 x y of {
     GT -> andb (ltb_tree0 x l) (ltb_tree0 x r);
     _ -> False}}

gtb_tree0 :: S3 -> Tree0 -> Bool
gtb_tree0 x s =
  case s of {
   Leaf0 -> True;
   Node0 _ l y r ->
    case compare12 x y of {
     LT -> andb (gtb_tree0 x l) (gtb_tree0 x r);
     _ -> False}}

isok0 :: Tree0 -> Bool
isok0 s =
  case s of {
   Leaf0 -> True;
   Node0 _ l x r ->
    andb (andb (andb (isok0 l) (isok0 r)) (ltb_tree0 x l)) (gtb_tree0 x r)}

type T14 = S3

compare15 :: S3 -> S3 -> Comparison
compare15 x y =
  case compare12 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec15 :: S3 -> S3 -> Sumbool
eq_dec15 =
  eq_dec14

type T15 = S3

compare16 :: S3 -> S3 -> Comparison
compare16 x y =
  case compare12 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec16 :: S3 -> S3 -> Sumbool
eq_dec16 =
  eq_dec15

eq_dec17 :: S3 -> S3 -> Sumbool
eq_dec17 =
  eq_dec14

lt_dec1 :: S3 -> S3 -> Sumbool
lt_dec1 x y =
  let {
   c = compSpec2Type x y
         (case compare12 x y of {
           LT -> Lt;
           EQ -> Eq;
           GT -> Gt})}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb4 :: S3 -> S3 -> Bool
eqb4 x y =
  case eq_dec17 x y of {
   Left -> True;
   Right -> False}

data R_min_elt0 =
   R_min_elt_3 Tree0
 | R_min_elt_4 Tree0 T Tree0 S3 Tree0
 | R_min_elt_5 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 (Option Elt2) 
 R_min_elt0
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_max_elt0 =
   R_max_elt_3 Tree0
 | R_max_elt_4 Tree0 T Tree0 S3 Tree0
 | R_max_elt_5 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 (Option Elt2) 
 R_max_elt0
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

type T16 = S3

compare17 :: S3 -> S3 -> Comparison
compare17 x y =
  case compare12 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec18 :: S3 -> S3 -> Sumbool
eq_dec18 =
  eq_dec14

type T17 = S3

compare18 :: S3 -> S3 -> Comparison
compare18 x y =
  case compare12 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec19 :: S3 -> S3 -> Sumbool
eq_dec19 =
  eq_dec18

eq_dec20 :: S3 -> S3 -> Sumbool
eq_dec20 =
  eq_dec14

lt_dec2 :: S3 -> S3 -> Sumbool
lt_dec2 x y =
  let {
   c = compSpec2Type x y
         (case compare12 x y of {
           LT -> Lt;
           EQ -> Eq;
           GT -> Gt})}
  in
  case c of {
   CompLtT -> Left;
   _ -> Right}

eqb5 :: S3 -> S3 -> Bool
eqb5 x y =
  case eq_dec20 x y of {
   Left -> True;
   Right -> False}

flatten_e0 :: Enumeration0 -> List Elt2
flatten_e0 e =
  case e of {
   End0 -> Nil;
   More0 x t r -> Cons x (app (elements2 t) (flatten_e0 r))}

data R_bal0 =
   R_bal_9 T13 S3 T13
 | R_bal_10 T13 S3 T13 T Tree0 S3 Tree0
 | R_bal_11 T13 S3 T13 T Tree0 S3 Tree0
 | R_bal_12 T13 S3 T13 T Tree0 S3 Tree0 T Tree0 S3 Tree0
 | R_bal_13 T13 S3 T13
 | R_bal_14 T13 S3 T13 T Tree0 S3 Tree0
 | R_bal_15 T13 S3 T13 T Tree0 S3 Tree0
 | R_bal_16 T13 S3 T13 T Tree0 S3 Tree0 T Tree0 S3 Tree0
 | R_bal_17 T13 S3 T13
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_remove_min0 =
   R_remove_min_2 Tree0 Elt2 T13
 | R_remove_min_3 Tree0 Elt2 T13 T Tree0 S3 Tree0 (Prod T13 Elt2) R_remove_min0 
 T13 Elt2
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_merge0 =
   R_merge_3 Tree0 Tree0
 | R_merge_4 Tree0 Tree0 T Tree0 S3 Tree0
 | R_merge_5 Tree0 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 T13 Elt2
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_concat0 =
   R_concat_3 Tree0 Tree0
 | R_concat_4 Tree0 Tree0 T Tree0 S3 Tree0
 | R_concat_5 Tree0 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 T13 Elt2
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_inter0 =
   R_inter_4 Tree0 Tree0
 | R_inter_5 Tree0 Tree0 T Tree0 S3 Tree0
 | R_inter_6 Tree0 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 T13 Bool T13 
 Tree0 R_inter0 Tree0 R_inter0
 | R_inter_7 Tree0 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 T13 Bool T13 
 Tree0 R_inter0 Tree0 R_inter0
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_diff0 =
   R_diff_4 Tree0 Tree0
 | R_diff_5 Tree0 Tree0 T Tree0 S3 Tree0
 | R_diff_6 Tree0 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 T13 Bool T13 
 Tree0 R_diff0 Tree0 R_diff0
 | R_diff_7 Tree0 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 T13 Bool T13 
 Tree0 R_diff0 Tree0 R_diff0
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

data R_union0 =
   R_union_3 Tree0 Tree0
 | R_union_4 Tree0 Tree0 T Tree0 S3 Tree0
 | R_union_5 Tree0 Tree0 T Tree0 S3 Tree0 T Tree0 S3 Tree0 T13 Bool T13 
 Tree0 R_union0 Tree0 R_union0
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

type T18 = S3

compare19 :: S3 -> S3 -> Comparison
compare19 x y =
  case compare12 x y of {
   LT -> Lt;
   EQ -> Eq;
   GT -> Gt}

eq_dec21 :: S3 -> S3 -> Sumbool
eq_dec21 =
  eq_dec14

type Elt3 = S3

type T_0 = T13
  -- singleton inductive, whose constructor was Mkt
  
this0 :: T_0 -> T13
this0 t =
  t

type T19 = T_0

mem3 :: Elt3 -> T19 -> Bool
mem3 x s =
  mem2 x (this0 s)

add6 :: Elt3 -> T19 -> T19
add6 x s =
  add5 x (this0 s)

remove3 :: Elt3 -> T19 -> T19
remove3 x s =
  remove2 x (this0 s)

singleton3 :: Elt3 -> T19
singleton3 =
  singleton2

union3 :: T19 -> T19 -> T19
union3 s s' =
  union2 (this0 s) (this0 s')

inter3 :: T19 -> T19 -> T19
inter3 s s' =
  inter2 (this0 s) (this0 s')

diff3 :: T19 -> T19 -> T19
diff3 s s' =
  diff2 (this0 s) (this0 s')

equal3 :: T19 -> T19 -> Bool
equal3 s s' =
  equal2 (this0 s) (this0 s')

subset3 :: T19 -> T19 -> Bool
subset3 s s' =
  subset2 (this0 s) (this0 s')

empty3 :: T19
empty3 =
  empty2

is_empty3 :: T19 -> Bool
is_empty3 s =
  is_empty2 (this0 s)

elements3 :: T19 -> List Elt3
elements3 s =
  elements2 (this0 s)

choose3 :: T19 -> Option Elt3
choose3 s =
  choose2 (this0 s)

fold3 :: (Elt3 -> a1 -> a1) -> T19 -> a1 -> a1
fold3 f s =
  fold2 f (this0 s)

cardinal3 :: T19 -> Nat
cardinal3 s =
  cardinal2 (this0 s)

filter4 :: (Elt3 -> Bool) -> T19 -> T19
filter4 f s =
  filter3 f (this0 s)

for_all3 :: (Elt3 -> Bool) -> T19 -> Bool
for_all3 f s =
  for_all2 f (this0 s)

exists_3 :: (Elt3 -> Bool) -> T19 -> Bool
exists_3 f s =
  exists_2 f (this0 s)

partition3 :: (Elt3 -> Bool) -> T19 -> Prod T19 T19
partition3 f s =
  let {p = partition2 f (this0 s)} in Pair (fst p) (snd p)

eq_dec22 :: T19 -> T19 -> Sumbool
eq_dec22 s0 s'0 =
  let {b = equal2 s0 s'0} in case b of {
                              True -> Left;
                              False -> Right}

compare20 :: T19 -> T19 -> Comparison
compare20 s s' =
  compare14 (this0 s) (this0 s')

min_elt3 :: T19 -> Option Elt3
min_elt3 s =
  min_elt2 (this0 s)

max_elt3 :: T19 -> Option Elt3
max_elt3 s =
  max_elt2 (this0 s)

type Elt4 = S3

type T20 = T19

empty4 :: T20
empty4 =
  empty3

is_empty4 :: T20 -> Bool
is_empty4 =
  is_empty3

mem4 :: Elt4 -> T20 -> Bool
mem4 =
  mem3

add7 :: Elt4 -> T20 -> T20
add7 =
  add6

singleton4 :: Elt4 -> T20
singleton4 =
  singleton3

remove4 :: Elt4 -> T20 -> T20
remove4 =
  remove3

union4 :: T20 -> T20 -> T20
union4 =
  union3

inter4 :: T20 -> T20 -> T20
inter4 =
  inter3

diff4 :: T20 -> T20 -> T20
diff4 =
  diff3

eq_dec23 :: T20 -> T20 -> Sumbool
eq_dec23 =
  eq_dec22

equal4 :: T20 -> T20 -> Bool
equal4 =
  equal3

subset4 :: T20 -> T20 -> Bool
subset4 =
  subset3

fold4 :: (Elt4 -> a1 -> a1) -> T20 -> a1 -> a1
fold4 =
  fold3

for_all4 :: (Elt4 -> Bool) -> T20 -> Bool
for_all4 =
  for_all3

exists_4 :: (Elt4 -> Bool) -> T20 -> Bool
exists_4 =
  exists_3

filter5 :: (Elt4 -> Bool) -> T20 -> T20
filter5 =
  filter4

partition4 :: (Elt4 -> Bool) -> T20 -> Prod T20 T20
partition4 =
  partition3

cardinal4 :: T20 -> Nat
cardinal4 =
  cardinal3

elements4 :: T20 -> List Elt4
elements4 =
  elements3

choose4 :: T20 -> Option Elt4
choose4 =
  choose3

eqb6 :: S3 -> S3 -> Bool
eqb6 x y =
  case eq_dec21 x y of {
   Left -> True;
   Right -> False}

min_elt4 :: T20 -> Option Elt4
min_elt4 =
  min_elt3

max_elt4 :: T20 -> Option Elt4
max_elt4 =
  max_elt3

compare21 :: T20 -> T20 -> Compare T20
compare21 s s' =
  let {c = compSpec2Type s s' (compare20 s s')} in
  case c of {
   CompEqT -> EQ;
   CompLtT -> LT;
   CompGtT -> GT}

type T21 = S3

compare22 :: S3 -> S3 -> Compare S3
compare22 =
  compare12

eq_dec24 :: S3 -> S3 -> Sumbool
eq_dec24 =
  eq_dec13

emptyRCSet :: T20
emptyRCSet =
  empty4

type S4 = Prod IdentPayT Person

type S5 = S4

st1 :: S5 -> List Prelude.Integer
st1 x =
  case x of {
   Pair i p -> Cons i (Cons p Nil)}

type T22 = S5

compareList1 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList1 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec1 :: T22 -> T22 -> Sumor Sumbool
compareDec1 x y =
  compareList1 (case x of {
                 Pair i p -> Cons i (Cons p Nil)})
    (case y of {
      Pair i p -> Cons i (Cons p Nil)})

compare23 :: T22 -> T22 -> Compare T22
compare23 x y =
  let {h = compareDec1 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec25 :: T22 -> T22 -> Sumbool
eq_dec25 x y =
  let {h = compareDec1 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type S6 = S4

st2 :: S6 -> List Prelude.Integer
st2 x =
  case x of {
   Pair i p -> Cons i (Cons p Nil)}

type T23 = S6

compareList2 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList2 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec2 :: T23 -> T23 -> Sumor Sumbool
compareDec2 x y =
  compareList2 (case x of {
                 Pair i p -> Cons i (Cons p Nil)})
    (case y of {
      Pair i p -> Cons i (Cons p Nil)})

compare24 :: T23 -> T23 -> Compare T23
compare24 x y =
  let {h = compareDec2 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec26 :: T23 -> T23 -> Sumbool
eq_dec26 x y =
  let {h = compareDec2 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type Key = S5

data Tree1 elt =
   Leaf1
 | Node1 (Tree1 elt) Key elt (Tree1 elt) T
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

tree_rect :: a2 -> ((Tree1 a1) -> a2 -> Key -> a1 -> (Tree1 a1) -> a2 -> T ->
             a2) -> (Tree1 a1) -> a2
tree_rect f f0 t =
  case t of {
   Leaf1 -> f;
   Node1 t0 k e t1 t2 ->
    f0 t0 (tree_rect f f0 t0) k e t1 (tree_rect f f0 t1) t2}

tree_rec :: a2 -> ((Tree1 a1) -> a2 -> Key -> a1 -> (Tree1 a1) -> a2 -> T ->
            a2) -> (Tree1 a1) -> a2
tree_rec =
  tree_rect

height1 :: (Tree1 a1) -> T
height1 m =
  case m of {
   Leaf1 -> _0;
   Node1 _ _ _ _ h -> h}

cardinal5 :: (Tree1 a1) -> Nat
cardinal5 m =
  case m of {
   Leaf1 -> O;
   Node1 l _ _ r _ -> S (add (cardinal5 l) (cardinal5 r))}

empty5 :: Tree1 a1
empty5 =
  Leaf1

is_empty5 :: (Tree1 a1) -> Bool
is_empty5 m =
  case m of {
   Leaf1 -> True;
   Node1 _ _ _ _ _ -> False}

mem5 :: S5 -> (Tree1 a1) -> Bool
mem5 x m =
  case m of {
   Leaf1 -> False;
   Node1 l y _ r _ ->
    case compare23 x y of {
     LT -> mem5 x l;
     EQ -> True;
     GT -> mem5 x r}}

find :: S5 -> (Tree1 a1) -> Option a1
find x m =
  case m of {
   Leaf1 -> None;
   Node1 l y d r _ ->
    case compare23 x y of {
     LT -> find x l;
     EQ -> Some d;
     GT -> find x r}}

create1 :: (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> Tree1 a1
create1 l x e r =
  Node1 l x e r (add1 (max0 (height1 l) (height1 r)) _1)

assert_false1 :: (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> Tree1 a1
assert_false1 =
  create1

bal1 :: (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> Tree1 a1
bal1 l x d r =
  let {hl = height1 l} in
  let {hr = height1 r} in
  case gt_le_dec hl (add1 hr _2) of {
   Left ->
    case l of {
     Leaf1 -> assert_false1 l x d r;
     Node1 ll lx ld lr _ ->
      case ge_lt_dec (height1 ll) (height1 lr) of {
       Left -> create1 ll lx ld (create1 lr x d r);
       Right ->
        case lr of {
         Leaf1 -> assert_false1 l x d r;
         Node1 lrl lrx lrd lrr _ ->
          create1 (create1 ll lx ld lrl) lrx lrd (create1 lrr x d r)}}};
   Right ->
    case gt_le_dec hr (add1 hl _2) of {
     Left ->
      case r of {
       Leaf1 -> assert_false1 l x d r;
       Node1 rl rx rd rr _ ->
        case ge_lt_dec (height1 rr) (height1 rl) of {
         Left -> create1 (create1 l x d rl) rx rd rr;
         Right ->
          case rl of {
           Leaf1 -> assert_false1 l x d r;
           Node1 rll rlx rld rlr _ ->
            create1 (create1 l x d rll) rlx rld (create1 rlr rx rd rr)}}};
     Right -> create1 l x d r}}

add8 :: Key -> a1 -> (Tree1 a1) -> Tree1 a1
add8 x d m =
  case m of {
   Leaf1 -> Node1 Leaf1 x d Leaf1 _1;
   Node1 l y d' r h ->
    case compare23 x y of {
     LT -> bal1 (add8 x d l) y d' r;
     EQ -> Node1 l y d r h;
     GT -> bal1 l y d' (add8 x d r)}}

remove_min1 :: (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> Prod (Tree1 a1)
               (Prod Key a1)
remove_min1 l x d r =
  case l of {
   Leaf1 -> Pair r (Pair x d);
   Node1 ll lx ld lr _ ->
    case remove_min1 ll lx ld lr of {
     Pair l' m -> Pair (bal1 l' x d r) m}}

merge1 :: (Tree1 a1) -> (Tree1 a1) -> Tree1 a1
merge1 s1 s2 =
  case s1 of {
   Leaf1 -> s2;
   Node1 _ _ _ _ _ ->
    case s2 of {
     Leaf1 -> s1;
     Node1 l2 x2 d2 r2 _ ->
      case remove_min1 l2 x2 d2 r2 of {
       Pair s2' p -> case p of {
                      Pair x d -> bal1 s1 x d s2'}}}}

remove5 :: S5 -> (Tree1 a1) -> Tree1 a1
remove5 x m =
  case m of {
   Leaf1 -> Leaf1;
   Node1 l y d r _ ->
    case compare23 x y of {
     LT -> bal1 (remove5 x l) y d r;
     EQ -> merge1 l r;
     GT -> bal1 l y d (remove5 x r)}}

join1 :: (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> Tree1 a1
join1 l =
  case l of {
   Leaf1 -> add8;
   Node1 ll lx ld lr lh -> (\x d ->
    let {
     join_aux r =
       case r of {
        Leaf1 -> add8 x d l;
        Node1 rl rx rd rr rh ->
         case gt_le_dec lh (add1 rh _2) of {
          Left -> bal1 ll lx ld (join1 lr x d r);
          Right ->
           case gt_le_dec rh (add1 lh _2) of {
            Left -> bal1 (join_aux rl) rx rd rr;
            Right -> create1 l x d r}}}}
    in join_aux)}

data Triple1 elt =
   Mktriple1 (Tree1 elt) (Option elt) (Tree1 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

t_left1 :: (Triple1 a1) -> Tree1 a1
t_left1 t =
  case t of {
   Mktriple1 t_left5 _ _ -> t_left5}

t_opt :: (Triple1 a1) -> Option a1
t_opt t =
  case t of {
   Mktriple1 _ t_opt3 _ -> t_opt3}

t_right1 :: (Triple1 a1) -> Tree1 a1
t_right1 t =
  case t of {
   Mktriple1 _ _ t_right5 -> t_right5}

split1 :: S5 -> (Tree1 a1) -> Triple1 a1
split1 x m =
  case m of {
   Leaf1 -> Mktriple1 Leaf1 None Leaf1;
   Node1 l y d r _ ->
    case compare23 x y of {
     LT ->
      case split1 x l of {
       Mktriple1 ll o rl -> Mktriple1 ll o (join1 rl y d r)};
     EQ -> Mktriple1 l (Some d) r;
     GT ->
      case split1 x r of {
       Mktriple1 rl o rr -> Mktriple1 (join1 l y d rl) o rr}}}

concat1 :: (Tree1 a1) -> (Tree1 a1) -> Tree1 a1
concat1 m1 m2 =
  case m1 of {
   Leaf1 -> m2;
   Node1 _ _ _ _ _ ->
    case m2 of {
     Leaf1 -> m1;
     Node1 l2 x2 d2 r2 _ ->
      case remove_min1 l2 x2 d2 r2 of {
       Pair m2' xd -> join1 m1 (fst xd) (snd xd) m2'}}}

elements_aux1 :: (List (Prod Key a1)) -> (Tree1 a1) -> List (Prod Key a1)
elements_aux1 acc m =
  case m of {
   Leaf1 -> acc;
   Node1 l x d r _ -> elements_aux1 (Cons (Pair x d) (elements_aux1 acc r)) l}

elements5 :: (Tree1 a1) -> List (Prod Key a1)
elements5 =
  elements_aux1 Nil

fold5 :: (Key -> a1 -> a2 -> a2) -> (Tree1 a1) -> a2 -> a2
fold5 f m a =
  case m of {
   Leaf1 -> a;
   Node1 l x d r _ -> fold5 f r (f x d (fold5 f l a))}

data Enumeration1 elt =
   End1
 | More1 Key elt (Tree1 elt) (Enumeration1 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

enumeration_rect :: a2 -> (Key -> a1 -> (Tree1 a1) -> (Enumeration1 a1) -> a2
                    -> a2) -> (Enumeration1 a1) -> a2
enumeration_rect f f0 e =
  case e of {
   End1 -> f;
   More1 k e0 t e1 -> f0 k e0 t e1 (enumeration_rect f f0 e1)}

enumeration_rec :: a2 -> (Key -> a1 -> (Tree1 a1) -> (Enumeration1 a1) -> a2
                   -> a2) -> (Enumeration1 a1) -> a2
enumeration_rec =
  enumeration_rect

cons1 :: (Tree1 a1) -> (Enumeration1 a1) -> Enumeration1 a1
cons1 m e =
  case m of {
   Leaf1 -> e;
   Node1 l x d r _ -> cons1 l (More1 x d r e)}

equal_more :: (a1 -> a1 -> Bool) -> S5 -> a1 -> ((Enumeration1 a1) -> Bool)
              -> (Enumeration1 a1) -> Bool
equal_more cmp x1 d1 cont e2 =
  case e2 of {
   End1 -> False;
   More1 x2 d2 r2 e3 ->
    case compare23 x1 x2 of {
     EQ -> case cmp d1 d2 of {
            True -> cont (cons1 r2 e3);
            False -> False};
     _ -> False}}

equal_cont :: (a1 -> a1 -> Bool) -> (Tree1 a1) -> ((Enumeration1 a1) -> Bool)
              -> (Enumeration1 a1) -> Bool
equal_cont cmp m1 cont e2 =
  case m1 of {
   Leaf1 -> cont e2;
   Node1 l1 x1 d1 r1 _ ->
    equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2}

equal_end :: (Enumeration1 a1) -> Bool
equal_end e2 =
  case e2 of {
   End1 -> True;
   More1 _ _ _ _ -> False}

equal5 :: (a1 -> a1 -> Bool) -> (Tree1 a1) -> (Tree1 a1) -> Bool
equal5 cmp m1 m2 =
  equal_cont cmp m1 equal_end (cons1 m2 End1)

map0 :: (a1 -> a2) -> (Tree1 a1) -> Tree1 a2
map0 f m =
  case m of {
   Leaf1 -> Leaf1;
   Node1 l x d r h -> Node1 (map0 f l) x (f d) (map0 f r) h}

mapi :: (Key -> a1 -> a2) -> (Tree1 a1) -> Tree1 a2
mapi f m =
  case m of {
   Leaf1 -> Leaf1;
   Node1 l x d r h -> Node1 (mapi f l) x (f x d) (mapi f r) h}

map_option :: (Key -> a1 -> Option a2) -> (Tree1 a1) -> Tree1 a2
map_option f m =
  case m of {
   Leaf1 -> Leaf1;
   Node1 l x d r _ ->
    case f x d of {
     Some d' -> join1 (map_option f l) x d' (map_option f r);
     None -> concat1 (map_option f l) (map_option f r)}}

map2_opt :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree1 a1) -> Tree1
            a3) -> ((Tree1 a2) -> Tree1 a3) -> (Tree1 a1) -> (Tree1 a2) ->
            Tree1 a3
map2_opt f mapl mapr m1 m2 =
  case m1 of {
   Leaf1 -> mapr m2;
   Node1 l1 x1 d1 r1 _ ->
    case m2 of {
     Leaf1 -> mapl m1;
     Node1 _ _ _ _ _ ->
      case split1 x1 m2 of {
       Mktriple1 l2' o2 r2' ->
        case f x1 d1 o2 of {
         Some e ->
          join1 (map2_opt f mapl mapr l1 l2') x1 e
            (map2_opt f mapl mapr r1 r2');
         None ->
          concat1 (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')}}}}

map2 :: ((Option a1) -> (Option a2) -> Option a3) -> (Tree1 a1) -> (Tree1 
        a2) -> Tree1 a3
map2 f =
  map2_opt (\_ d o -> f (Some d) o) (map_option (\_ d -> f (Some d) None))
    (map_option (\_ d' -> f None (Some d')))

type T24 = S5

eq_dec27 :: S5 -> S5 -> Sumbool
eq_dec27 =
  eq_dec25

lt_dec3 :: S5 -> S5 -> Sumbool
lt_dec3 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare23 x y)

eqb7 :: S5 -> S5 -> Bool
eqb7 x y =
  case eq_dec27 x y of {
   Left -> True;
   Right -> False}

type T25 = S5

eq_dec28 :: S5 -> S5 -> Sumbool
eq_dec28 =
  eq_dec25

lt_dec4 :: S5 -> S5 -> Sumbool
lt_dec4 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare23 x y)

eqb8 :: S5 -> S5 -> Bool
eqb8 x y =
  case eq_dec28 x y of {
   Left -> True;
   Right -> False}

type T26 = S5

eq_dec29 :: S5 -> S5 -> Sumbool
eq_dec29 =
  eq_dec25

lt_dec5 :: S5 -> S5 -> Sumbool
lt_dec5 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare23 x y)

eqb9 :: S5 -> S5 -> Bool
eqb9 x y =
  case eq_dec29 x y of {
   Left -> True;
   Right -> False}

type T27 = S5

eq_dec30 :: S5 -> S5 -> Sumbool
eq_dec30 =
  eq_dec25

lt_dec6 :: S5 -> S5 -> Sumbool
lt_dec6 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare23 x y)

eqb10 :: S5 -> S5 -> Bool
eqb10 x y =
  case eq_dec30 x y of {
   Left -> True;
   Right -> False}

type Key0 = S5

type T28 elt = List (Prod S5 elt)

empty6 :: T28 a1
empty6 =
  Nil

is_empty6 :: (T28 a1) -> Bool
is_empty6 l =
  case l of {
   Nil -> True;
   Cons _ _ -> False}

mem6 :: Key0 -> (T28 a1) -> Bool
mem6 k s =
  case s of {
   Nil -> False;
   Cons p l ->
    case p of {
     Pair k' _ ->
      case compare23 k k' of {
       LT -> False;
       EQ -> True;
       GT -> mem6 k l}}}

data R_mem elt =
   R_mem_0 (T28 elt)
 | R_mem_1 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_mem_2 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_mem_3 (T28 elt) S5 elt (List (Prod S5 elt)) Bool (R_mem elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
              (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5
              -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28
              a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () ->
              Bool -> (R_mem a1) -> a2 -> a2) -> (T28 a1) -> Bool -> (R_mem
              a1) -> a2
r_mem_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_mem_0 s -> f s __;
   R_mem_1 s k' _x l -> f0 s k' _x l __ __ __;
   R_mem_2 s k' _x l -> f1 s k' _x l __ __ __;
   R_mem_3 s k' _x l _res r0 ->
    f2 s k' _x l __ __ __ _res r0 (r_mem_rect k f f0 f1 f2 l _res r0)}

r_mem_rec :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 -> (List
             (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5 -> a1
             -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
             a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> Bool
             -> (R_mem a1) -> a2 -> a2) -> (T28 a1) -> Bool -> (R_mem 
             a1) -> a2
r_mem_rec =
  r_mem_rect

mem_rect :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 -> (List
            (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5 -> a1
            -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
            a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2 ->
            a2) -> (T28 a1) -> a2
mem_rect k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> False;
      Cons p l ->
       case p of {
        Pair k' _ ->
         case compare23 k k' of {
          LT -> False;
          EQ -> True;
          GT -> mem6 k l}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ -> let {hrec = mem_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare23 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (mem6 k s)

mem_rec :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 -> (List
           (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
           (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5 ->
           a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2 -> a2) -> (T28
           a1) -> a2
mem_rec =
  mem_rect

r_mem_correct :: Key0 -> (T28 a1) -> Bool -> R_mem a1
r_mem_correct k s _res =
  unsafeCoerce mem_rect k (\y _ z _ -> eq_rect_r False (R_mem_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r False (R_mem_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r True (R_mem_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (mem6 k y2) (R_mem_3 y y0 y1 y2 (mem6 k y2)
      (y6 (mem6 k y2) __)) z) s _res __

find0 :: Key0 -> (T28 a1) -> Option a1
find0 k s =
  case s of {
   Nil -> None;
   Cons p s' ->
    case p of {
     Pair k' x ->
      case compare23 k k' of {
       LT -> None;
       EQ -> Some x;
       GT -> find0 k s'}}}

data R_find elt =
   R_find_0 (T28 elt)
 | R_find_1 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_find_2 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_find_3 (T28 elt) S5 elt (List (Prod S5 elt)) (Option elt) (R_find elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
               (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
               a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () ->
               a2) -> ((T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () ->
               () -> () -> (Option a1) -> (R_find a1) -> a2 -> a2) -> (T28
               a1) -> (Option a1) -> (R_find a1) -> a2
r_find_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_find_0 s -> f s __;
   R_find_1 s k' x s' -> f0 s k' x s' __ __ __;
   R_find_2 s k' x s' -> f1 s k' x s' __ __ __;
   R_find_3 s k' x s' _res r0 ->
    f2 s k' x s' __ __ __ _res r0 (r_find_rect k f f0 f1 f2 s' _res r0)}

r_find_rec :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
              (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5
              -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28
              a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () ->
              (Option a1) -> (R_find a1) -> a2 -> a2) -> (T28 a1) -> (Option
              a1) -> (R_find a1) -> a2
r_find_rec =
  r_find_rect

find_rect :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 -> (List
             (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5 -> a1
             -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
             a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2
             -> a2) -> (T28 a1) -> a2
find_rect k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> None;
      Cons p s' ->
       case p of {
        Pair k' x ->
         case compare23 k k' of {
          LT -> None;
          EQ -> Some x;
          GT -> find0 k s'}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = find_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare23 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (find0 k s)

find_rec :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 -> (List
            (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5 -> a1
            -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
            a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2 ->
            a2) -> (T28 a1) -> a2
find_rec =
  find_rect

r_find_correct :: Key0 -> (T28 a1) -> (Option a1) -> R_find a1
r_find_correct k s _res =
  unsafeCoerce find_rect k (\y _ z _ -> eq_rect_r None (R_find_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r None (R_find_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r (Some y1) (R_find_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (find0 k y2) (R_find_3 y y0 y1 y2 (find0 k y2)
      (y6 (find0 k y2) __)) z) s _res __

add9 :: Key0 -> a1 -> (T28 a1) -> T28 a1
add9 k x s =
  case s of {
   Nil -> Cons (Pair k x) Nil;
   Cons p l ->
    case p of {
     Pair k' y ->
      case compare23 k k' of {
       LT -> Cons (Pair k x) s;
       EQ -> Cons (Pair k x) l;
       GT -> Cons (Pair k' y) (add9 k x l)}}}

data R_add elt =
   R_add_0 (T28 elt)
 | R_add_1 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_add_2 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_add_3 (T28 elt) S5 elt (List (Prod S5 elt)) (T28 elt) (R_add elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect :: Key0 -> a1 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1
              -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
              a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2)
              -> ((T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () ->
              () -> (T28 a1) -> (R_add a1) -> a2 -> a2) -> (T28 a1) -> (T28
              a1) -> (R_add a1) -> a2
r_add_rect k x f f0 f1 f2 _ _ r =
  case r of {
   R_add_0 s -> f s __;
   R_add_1 s k' y l -> f0 s k' y l __ __ __;
   R_add_2 s k' y l -> f1 s k' y l __ __ __;
   R_add_3 s k' y l _res r0 ->
    f2 s k' y l __ __ __ _res r0 (r_add_rect k x f f0 f1 f2 l _res r0)}

r_add_rec :: Key0 -> a1 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
             (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5
             -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28
             a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> (T28
             a1) -> (R_add a1) -> a2 -> a2) -> (T28 a1) -> (T28 a1) -> (R_add
             a1) -> a2
r_add_rec =
  r_add_rect

add_rect :: Key0 -> a1 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
            (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5
            -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28
            a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2 ->
            a2) -> (T28 a1) -> a2
add_rect k x f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Cons (Pair k x) Nil;
      Cons p l ->
       case p of {
        Pair k' y ->
         case compare23 k k' of {
          LT -> Cons (Pair k x) s;
          EQ -> Cons (Pair k x) l;
          GT -> Cons (Pair k' y) (add9 k x l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = add_rect k x f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare23 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (add9 k x s)

add_rec :: Key0 -> a1 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
           (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5 ->
           a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
           a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2 ->
           a2) -> (T28 a1) -> a2
add_rec =
  add_rect

r_add_correct :: Key0 -> a1 -> (T28 a1) -> (T28 a1) -> R_add a1
r_add_correct k x s _res =
  add_rect k x (\y _ z _ -> eq_rect_r (Cons (Pair k x) Nil) (R_add_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y) (R_add_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y2) (R_add_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (add9 k x y2)) (R_add_3 y y0 y1 y2
      (add9 k x y2) (y6 (add9 k x y2) __)) z) s _res __

remove6 :: Key0 -> (T28 a1) -> T28 a1
remove6 k s =
  case s of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k' x ->
      case compare23 k k' of {
       LT -> s;
       EQ -> l;
       GT -> Cons (Pair k' x) (remove6 k l)}}}

data R_remove elt =
   R_remove_0 (T28 elt)
 | R_remove_1 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_remove_2 (T28 elt) S5 elt (List (Prod S5 elt))
 | R_remove_3 (T28 elt) S5 elt (List (Prod S5 elt)) (T28 elt) (R_remove elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
                 (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
                 a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () ->
                 a2) -> ((T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () ->
                 () -> () -> (T28 a1) -> (R_remove a1) -> a2 -> a2) -> (T28
                 a1) -> (T28 a1) -> (R_remove a1) -> a2
r_remove_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_remove_0 s -> f s __;
   R_remove_1 s k' x l -> f0 s k' x l __ __ __;
   R_remove_2 s k' x l -> f1 s k' x l __ __ __;
   R_remove_3 s k' x l _res r0 ->
    f2 s k' x l __ __ __ _res r0 (r_remove_rect k f f0 f1 f2 l _res r0)}

r_remove_rec :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
                (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
                a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () ->
                a2) -> ((T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () ->
                () -> () -> (T28 a1) -> (R_remove a1) -> a2 -> a2) -> (T28
                a1) -> (T28 a1) -> (R_remove a1) -> a2
r_remove_rec =
  r_remove_rect

remove_rect :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
               (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 
               a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () ->
               a2) -> ((T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () ->
               () -> () -> a2 -> a2) -> (T28 a1) -> a2
remove_rect k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Nil;
      Cons p l ->
       case p of {
        Pair k' x ->
         case compare23 k k' of {
          LT -> s;
          EQ -> l;
          GT -> Cons (Pair k' x) (remove6 k l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = remove_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare23 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (remove6 k s)

remove_rec :: Key0 -> ((T28 a1) -> () -> a2) -> ((T28 a1) -> S5 -> a1 ->
              (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28 a1) -> S5
              -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2) -> ((T28
              a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2
              -> a2) -> (T28 a1) -> a2
remove_rec =
  remove_rect

r_remove_correct :: Key0 -> (T28 a1) -> (T28 a1) -> R_remove a1
r_remove_correct k s _res =
  unsafeCoerce remove_rect k (\y _ z _ -> eq_rect_r Nil (R_remove_0 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y (R_remove_1 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y2 (R_remove_2 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (remove6 k y2)) (R_remove_3 y y0 y1 y2
      (remove6 k y2) (y6 (remove6 k y2) __)) z) s _res __

elements6 :: (T28 a1) -> T28 a1
elements6 m =
  m

fold6 :: (Key0 -> a1 -> a2 -> a2) -> (T28 a1) -> a2 -> a2
fold6 f m acc =
  case m of {
   Nil -> acc;
   Cons p m' -> case p of {
                 Pair k e -> fold6 f m' (f k e acc)}}

data R_fold elt a =
   R_fold_0 (T28 elt) a
 | R_fold_1 (T28 elt) a S5 elt (List (Prod S5 elt)) a (R_fold elt a)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_fold_rect :: (Key0 -> a1 -> a2 -> a2) -> ((T28 a1) -> a2 -> () -> a3) ->
               ((T28 a1) -> a2 -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> a2
               -> (R_fold a1 a2) -> a3 -> a3) -> (T28 a1) -> a2 -> a2 ->
               (R_fold a1 a2) -> a3
r_fold_rect f f0 f1 _ _ _ r =
  case r of {
   R_fold_0 m acc -> f0 m acc __;
   R_fold_1 m acc k e m' _res r0 ->
    f1 m acc k e m' __ _res r0 (r_fold_rect f f0 f1 m' (f k e acc) _res r0)}

r_fold_rec :: (Key0 -> a1 -> a2 -> a2) -> ((T28 a1) -> a2 -> () -> a3) ->
              ((T28 a1) -> a2 -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> a2
              -> (R_fold a1 a2) -> a3 -> a3) -> (T28 a1) -> a2 -> a2 ->
              (R_fold a1 a2) -> a3
r_fold_rec =
  r_fold_rect

fold_rect :: (Key0 -> a1 -> a2 -> a2) -> ((T28 a1) -> a2 -> () -> a3) ->
             ((T28 a1) -> a2 -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> a3
             -> a3) -> (T28 a1) -> a2 -> a3
fold_rect f1 f0 f m acc =
  eq_rect_r
    (case m of {
      Nil -> acc;
      Cons p m' -> case p of {
                    Pair k e -> fold6 f1 m' (f1 k e acc)}})
    (let {f2 = f0 m acc} in
     let {f3 = f m acc} in
     case m of {
      Nil -> f2 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f4 = f3 t0 e l __} in
         let {hrec = fold_rect f1 f0 f l (f1 t0 e acc)} in f4 hrec}})
    (fold6 f1 m acc)

fold_rec :: (Key0 -> a1 -> a2 -> a2) -> ((T28 a1) -> a2 -> () -> a3) -> ((T28
            a1) -> a2 -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> a3 -> a3)
            -> (T28 a1) -> a2 -> a3
fold_rec =
  fold_rect

r_fold_correct :: (Key0 -> a1 -> a2 -> a2) -> (T28 a1) -> a2 -> a2 -> R_fold
                  a1 a2
r_fold_correct f m acc _res =
  fold_rect f (\y y0 _ z _ -> eq_rect_r y0 (R_fold_0 y y0) z)
    (\y y0 y1 y2 y3 _ y5 z _ ->
    eq_rect_r (fold6 f y3 (f y1 y2 y0)) (R_fold_1 y y0 y1 y2 y3
      (fold6 f y3 (f y1 y2 y0)) (y5 (fold6 f y3 (f y1 y2 y0)) __)) z) m acc
    _res __

equal6 :: (a1 -> a1 -> Bool) -> (T28 a1) -> (T28 a1) -> Bool
equal6 cmp m m' =
  case m of {
   Nil -> case m' of {
           Nil -> True;
           Cons _ _ -> False};
   Cons p l ->
    case p of {
     Pair x e ->
      case m' of {
       Nil -> False;
       Cons p0 l' ->
        case p0 of {
         Pair x' e' ->
          case compare23 x x' of {
           EQ -> andb (cmp e e') (equal6 cmp l l');
           _ -> False}}}}}

data R_equal elt =
   R_equal_0 (T28 elt) (T28 elt)
 | R_equal_1 (T28 elt) (T28 elt) S5 elt (List (Prod S5 elt)) S5 elt (List
                                                                    (Prod 
                                                                    S5 
                                                                    elt)) 
 Bool (R_equal elt)
 | R_equal_2 (T28 elt) (T28 elt) S5 elt (List (Prod S5 elt)) S5 elt (List
                                                                    (Prod 
                                                                    S5 
                                                                    elt)) 
 (Compare S5)
 | R_equal_3 (T28 elt) (T28 elt) (T28 elt) (T28 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_equal_rect :: (a1 -> a1 -> Bool) -> ((T28 a1) -> (T28 a1) -> () -> () ->
                a2) -> ((T28 a1) -> (T28 a1) -> S5 -> a1 -> (List
                (Prod S5 a1)) -> () -> S5 -> a1 -> (List (Prod S5 a1)) -> ()
                -> () -> () -> Bool -> (R_equal a1) -> a2 -> a2) -> ((T28 
                a1) -> (T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () ->
                S5 -> a1 -> (List (Prod S5 a1)) -> () -> (Compare S5) -> ()
                -> () -> a2) -> ((T28 a1) -> (T28 a1) -> (T28 a1) -> () ->
                (T28 a1) -> () -> () -> a2) -> (T28 a1) -> (T28 a1) -> Bool
                -> (R_equal a1) -> a2
r_equal_rect cmp f f0 f1 f2 _ _ _ r =
  case r of {
   R_equal_0 m m' -> f m m' __ __;
   R_equal_1 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (r_equal_rect cmp f f0 f1 f2 l l' _res r0);
   R_equal_2 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   R_equal_3 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

r_equal_rec :: (a1 -> a1 -> Bool) -> ((T28 a1) -> (T28 a1) -> () -> () -> a2)
               -> ((T28 a1) -> (T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) ->
               () -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () ->
               Bool -> (R_equal a1) -> a2 -> a2) -> ((T28 a1) -> (T28 
               a1) -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> S5 -> a1 ->
               (List (Prod S5 a1)) -> () -> (Compare S5) -> () -> () -> a2)
               -> ((T28 a1) -> (T28 a1) -> (T28 a1) -> () -> (T28 a1) -> ()
               -> () -> a2) -> (T28 a1) -> (T28 a1) -> Bool -> (R_equal 
               a1) -> a2
r_equal_rec =
  r_equal_rect

equal_rect :: (a1 -> a1 -> Bool) -> ((T28 a1) -> (T28 a1) -> () -> () -> a2)
              -> ((T28 a1) -> (T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) ->
              () -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2
              -> a2) -> ((T28 a1) -> (T28 a1) -> S5 -> a1 -> (List
              (Prod S5 a1)) -> () -> S5 -> a1 -> (List (Prod S5 a1)) -> () ->
              (Compare S5) -> () -> () -> a2) -> ((T28 a1) -> (T28 a1) ->
              (T28 a1) -> () -> (T28 a1) -> () -> () -> a2) -> (T28 a1) ->
              (T28 a1) -> a2
equal_rect cmp f2 f1 f0 f m m' =
  eq_rect_r
    (case m of {
      Nil -> case m' of {
              Nil -> True;
              Cons _ _ -> False};
      Cons p l ->
       case p of {
        Pair x e ->
         case m' of {
          Nil -> False;
          Cons p0 l' ->
           case p0 of {
            Pair x' e' ->
             case compare23 x x' of {
              EQ -> andb (cmp e e') (equal6 cmp l l');
              _ -> False}}}}})
    (let {f3 = f2 m m'} in
     let {f4 = f1 m m'} in
     let {f5 = f0 m m'} in
     let {f6 = f m m'} in
     let {f7 = f6 m __} in
     let {f8 = f7 m' __} in
     case m of {
      Nil ->
       let {f9 = f3 __} in case m' of {
                            Nil -> f9 __;
                            Cons _ _ -> f8 __};
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case m' of {
          Nil -> f8 __;
          Cons p0 l0 ->
           case p0 of {
            Pair t1 e0 ->
             let {f11 = f9 t1 e0 l0 __} in
             let {f12 = let {_x = compare23 t0 t1} in f11 _x __} in
             let {f13 = f10 t1 e0 l0 __} in
             let {
              f14 = \_ _ ->
               let {hrec = equal_rect cmp f2 f1 f0 f l l0} in f13 __ __ hrec}
             in
             case compare23 t0 t1 of {
              EQ -> f14 __ __;
              _ -> f12 __}}}}}) (equal6 cmp m m')

equal_rec :: (a1 -> a1 -> Bool) -> ((T28 a1) -> (T28 a1) -> () -> () -> a2)
             -> ((T28 a1) -> (T28 a1) -> S5 -> a1 -> (List (Prod S5 a1)) ->
             () -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> () -> () -> a2 ->
             a2) -> ((T28 a1) -> (T28 a1) -> S5 -> a1 -> (List (Prod S5 a1))
             -> () -> S5 -> a1 -> (List (Prod S5 a1)) -> () -> (Compare 
             S5) -> () -> () -> a2) -> ((T28 a1) -> (T28 a1) -> (T28 
             a1) -> () -> (T28 a1) -> () -> () -> a2) -> (T28 a1) -> (T28 
             a1) -> a2
equal_rec =
  equal_rect

r_equal_correct :: (a1 -> a1 -> Bool) -> (T28 a1) -> (T28 a1) -> Bool ->
                   R_equal a1
r_equal_correct cmp m m' _res =
  equal_rect cmp (\y y0 _ _ z _ -> eq_rect_r True (R_equal_0 y y0) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ ->
    eq_rect_r (andb (cmp y2 y6) (equal6 cmp y3 y7)) (R_equal_1 y y0 y1 y2 y3
      y5 y6 y7 (equal6 cmp y3 y7) (y11 (equal6 cmp y3 y7) __)) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ ->
    eq_rect_r False (R_equal_2 y y0 y1 y2 y3 y5 y6 y7 y9) z)
    (\y y0 y1 _ y3 _ _ z _ -> eq_rect_r False (R_equal_3 y y0 y1 y3) z) m m'
    _res __

map1 :: (a1 -> a2) -> (T28 a1) -> T28 a2
map1 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f e)) (map1 f m')}}

mapi0 :: (Key0 -> a1 -> a2) -> (T28 a1) -> T28 a2
mapi0 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f k e)) (mapi0 f m')}}

option_cons :: Key0 -> (Option a1) -> (List (Prod Key0 a1)) -> List
               (Prod Key0 a1)
option_cons k o l =
  case o of {
   Some e -> Cons (Pair k e) l;
   None -> l}

map2_l :: ((Option a1) -> (Option a2) -> Option a3) -> (T28 a1) -> T28 a3
map2_l f m =
  case m of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k e -> option_cons k (f (Some e) None) (map2_l f l)}}

map2_r :: ((Option a1) -> (Option a2) -> Option a3) -> (T28 a2) -> T28 a3
map2_r f m' =
  case m' of {
   Nil -> Nil;
   Cons p l' ->
    case p of {
     Pair k e' -> option_cons k (f None (Some e')) (map2_r f l')}}

map3 :: ((Option a1) -> (Option a2) -> Option a3) -> (T28 a1) -> (T28 
        a2) -> T28 a3
map3 f m =
  case m of {
   Nil -> map2_r f;
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       map2_aux m' =
         case m' of {
          Nil -> map2_l f m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare23 k k' of {
              LT -> option_cons k (f (Some e) None) (map3 f l m');
              EQ -> option_cons k (f (Some e) (Some e')) (map3 f l l');
              GT -> option_cons k' (f None (Some e')) (map2_aux l')}}}}
      in map2_aux}}

combine :: (T28 a1) -> (T28 a2) -> T28 (Prod (Option a1) (Option a2))
combine m =
  case m of {
   Nil -> map1 (\e' -> Pair None (Some e'));
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       combine_aux m' =
         case m' of {
          Nil -> map1 (\e0 -> Pair (Some e0) None) m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare23 k k' of {
              LT -> Cons (Pair k (Pair (Some e) None)) (combine l m');
              EQ -> Cons (Pair k (Pair (Some e) (Some e'))) (combine l l');
              GT -> Cons (Pair k' (Pair None (Some e'))) (combine_aux l')}}}}
      in combine_aux}}

fold_right_pair :: (a1 -> a2 -> a3 -> a3) -> (List (Prod a1 a2)) -> a3 -> a3
fold_right_pair f l i =
  fold_right (\p -> f (fst p) (snd p)) i l

map2_alt :: ((Option a1) -> (Option a2) -> Option a3) -> (T28 a1) -> (T28 
            a2) -> List (Prod Key0 a3)
map2_alt f m m' =
  let {m0 = combine m m'} in
  let {m1 = map1 (\p -> f (fst p) (snd p)) m0} in
  fold_right_pair option_cons m1 Nil

at_least_one :: (Option a1) -> (Option a2) -> Option
                (Prod (Option a1) (Option a2))
at_least_one o o' =
  case o of {
   Some _ -> Some (Pair o o');
   None -> case o' of {
            Some _ -> Some (Pair o o');
            None -> None}}

at_least_one_then_f :: ((Option a1) -> (Option a2) -> Option a3) -> (Option
                       a1) -> (Option a2) -> Option a3
at_least_one_then_f f o o' =
  case o of {
   Some _ -> f o o';
   None -> case o' of {
            Some _ -> f o o';
            None -> None}}

data R_mem0 elt =
   R_mem_4 (Tree1 elt)
 | R_mem_5 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T Bool (R_mem0 elt)
 | R_mem_6 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T
 | R_mem_7 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T Bool (R_mem0 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect0 :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
               a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> Bool
               -> (R_mem0 a1) -> a2 -> a2) -> ((Tree1 a1) -> (Tree1 a1) ->
               Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> a2) ->
               ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T ->
               () -> () -> () -> Bool -> (R_mem0 a1) -> a2 -> a2) -> (Tree1
               a1) -> Bool -> (R_mem0 a1) -> a2
r_mem_rect0 x f f0 f1 f2 _ _ r =
  case r of {
   R_mem_4 m -> f m __;
   R_mem_5 m l y _x r0 _x0 _res r1 ->
    f0 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect0 x f f0 f1 f2 l _res r1);
   R_mem_6 m l y _x r0 _x0 -> f1 m l y _x r0 _x0 __ __ __;
   R_mem_7 m l y _x r0 _x0 _res r1 ->
    f2 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect0 x f f0 f1 f2 r0 _res r1)}

r_mem_rec0 :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
              a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> Bool
              -> (R_mem0 a1) -> a2 -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> Key
              -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> a2) -> ((Tree1
              a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> ()
              -> () -> Bool -> (R_mem0 a1) -> a2 -> a2) -> (Tree1 a1) -> Bool
              -> (R_mem0 a1) -> a2
r_mem_rec0 =
  r_mem_rect0

data R_find0 elt =
   R_find_4 (Tree1 elt)
 | R_find_5 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Option elt) 
 (R_find0 elt)
 | R_find_6 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T
 | R_find_7 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Option elt) 
 (R_find0 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect0 :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
                a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
                (Option a1) -> (R_find0 a1) -> a2 -> a2) -> ((Tree1 a1) ->
                (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> ()
                -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1
                a1) -> T -> () -> () -> () -> (Option a1) -> (R_find0 
                a1) -> a2 -> a2) -> (Tree1 a1) -> (Option a1) -> (R_find0 
                a1) -> a2
r_find_rect0 x f f0 f1 f2 _ _ r =
  case r of {
   R_find_4 m -> f m __;
   R_find_5 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_find_rect0 x f f0 f1 f2 l _res r1);
   R_find_6 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_find_7 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_find_rect0 x f f0 f1 f2 r0 _res r1)}

r_find_rec0 :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
               a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
               (Option a1) -> (R_find0 a1) -> a2 -> a2) -> ((Tree1 a1) ->
               (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 
               a1) -> T -> () -> () -> () -> (Option a1) -> (R_find0 
               a1) -> a2 -> a2) -> (Tree1 a1) -> (Option a1) -> (R_find0 
               a1) -> a2
r_find_rec0 =
  r_find_rect0

data R_bal1 elt =
   R_bal_18 (Tree1 elt) Key elt (Tree1 elt)
 | R_bal_19 (Tree1 elt) Key elt (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T
 | R_bal_20 (Tree1 elt) Key elt (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T
 | R_bal_21 (Tree1 elt) Key elt (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T (Tree1 elt) Key elt (Tree1 elt) T
 | R_bal_22 (Tree1 elt) Key elt (Tree1 elt)
 | R_bal_23 (Tree1 elt) Key elt (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T
 | R_bal_24 (Tree1 elt) Key elt (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T
 | R_bal_25 (Tree1 elt) Key elt (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T (Tree1 elt) Key elt (Tree1 elt) T
 | R_bal_26 (Tree1 elt) Key elt (Tree1 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_bal_rect :: ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> () -> a2)
              -> ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> (Tree1
              a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> (Tree1
              a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> () ->
              a2) -> ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () ->
              (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
              (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> a2) ->
              ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> () -> ()
              -> () -> a2) -> ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () ->
              () -> () -> () -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T ->
              () -> () -> () -> a2) -> ((Tree1 a1) -> Key -> a1 -> (Tree1 
              a1) -> () -> () -> () -> () -> (Tree1 a1) -> Key -> a1 ->
              (Tree1 a1) -> T -> () -> () -> () -> () -> a2) -> ((Tree1 
              a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> () -> () ->
              (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
              (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> a2) ->
              ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> () -> ()
              -> a2) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> (Tree1 
              a1) -> (R_bal1 a1) -> a2
r_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ r =
  case r of {
   R_bal_18 x x0 x1 x2 -> f x x0 x1 x2 __ __ __;
   R_bal_19 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_20 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_21 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_22 x x0 x1 x2 -> f3 x x0 x1 x2 __ __ __ __ __;
   R_bal_23 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_24 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_25 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_26 x x0 x1 x2 -> f7 x x0 x1 x2 __ __ __ __}

r_bal_rec :: ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> () -> a2)
             -> ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> (Tree1
             a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> a2) ->
             ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> (Tree1 
             a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> () ->
             a2) -> ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () ->
             (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
             (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> a2) ->
             ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> () -> () -> ()
             -> () -> a2) -> ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () ->
             () -> () -> () -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T ->
             () -> () -> () -> a2) -> ((Tree1 a1) -> Key -> a1 -> (Tree1 
             a1) -> () -> () -> () -> () -> (Tree1 a1) -> Key -> a1 -> (Tree1
             a1) -> T -> () -> () -> () -> () -> a2) -> ((Tree1 a1) -> Key ->
             a1 -> (Tree1 a1) -> () -> () -> () -> () -> (Tree1 a1) -> Key ->
             a1 -> (Tree1 a1) -> T -> () -> () -> () -> (Tree1 a1) -> Key ->
             a1 -> (Tree1 a1) -> T -> () -> a2) -> ((Tree1 a1) -> Key -> a1
             -> (Tree1 a1) -> () -> () -> () -> () -> a2) -> (Tree1 a1) ->
             Key -> a1 -> (Tree1 a1) -> (Tree1 a1) -> (R_bal1 a1) -> a2
r_bal_rec =
  r_bal_rect

data R_add0 elt =
   R_add_4 (Tree1 elt)
 | R_add_5 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Tree1 elt) 
 (R_add0 elt)
 | R_add_6 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T
 | R_add_7 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Tree1 elt) 
 (R_add0 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect0 :: Key -> a1 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1
               a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
               (Tree1 a1) -> (R_add0 a1) -> a2 -> a2) -> ((Tree1 a1) ->
               (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 
               a1) -> T -> () -> () -> () -> (Tree1 a1) -> (R_add0 a1) -> a2
               -> a2) -> (Tree1 a1) -> (Tree1 a1) -> (R_add0 a1) -> a2
r_add_rect0 x d f f0 f1 f2 _ _ r =
  case r of {
   R_add_4 m -> f m __;
   R_add_5 m l y d' r0 h _res r1 ->
    f0 m l y d' r0 h __ __ __ _res r1 (r_add_rect0 x d f f0 f1 f2 l _res r1);
   R_add_6 m l y d' r0 h -> f1 m l y d' r0 h __ __ __;
   R_add_7 m l y d' r0 h _res r1 ->
    f2 m l y d' r0 h __ __ __ _res r1 (r_add_rect0 x d f f0 f1 f2 r0 _res r1)}

r_add_rec0 :: Key -> a1 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1
              a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> (Tree1
              a1) -> (R_add0 a1) -> a2 -> a2) -> ((Tree1 a1) -> (Tree1 
              a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> ()
              -> () -> () -> (Tree1 a1) -> (R_add0 a1) -> a2 -> a2) -> (Tree1
              a1) -> (Tree1 a1) -> (R_add0 a1) -> a2
r_add_rec0 =
  r_add_rect0

data R_remove_min1 elt =
   R_remove_min_4 (Tree1 elt) Key elt (Tree1 elt)
 | R_remove_min_5 (Tree1 elt) Key elt (Tree1 elt) (Tree1 elt) Key elt 
 (Tree1 elt) T (Prod (Tree1 elt) (Prod Key elt)) (R_remove_min1 elt) 
 (Tree1 elt) (Prod Key elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_min_rect :: ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> a2) ->
                     ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> (Tree1 
                     a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Prod
                     (Tree1 a1) (Prod Key a1)) -> (R_remove_min1 a1) -> a2 ->
                     (Tree1 a1) -> (Prod Key a1) -> () -> a2) -> (Tree1 
                     a1) -> Key -> a1 -> (Tree1 a1) -> (Prod (Tree1 a1)
                     (Prod Key a1)) -> (R_remove_min1 a1) -> a2
r_remove_min_rect f f0 _ _ _ _ _ r =
  case r of {
   R_remove_min_4 l x d r0 -> f l x d r0 __;
   R_remove_min_5 l x d r0 ll lx ld lr _x _res r1 l' m ->
    f0 l x d r0 ll lx ld lr _x __ _res r1
      (r_remove_min_rect f f0 ll lx ld lr _res r1) l' m __}

r_remove_min_rec :: ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> () -> a2) ->
                    ((Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> (Tree1 
                    a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Prod
                    (Tree1 a1) (Prod Key a1)) -> (R_remove_min1 a1) -> a2 ->
                    (Tree1 a1) -> (Prod Key a1) -> () -> a2) -> (Tree1 
                    a1) -> Key -> a1 -> (Tree1 a1) -> (Prod (Tree1 a1)
                    (Prod Key a1)) -> (R_remove_min1 a1) -> a2
r_remove_min_rec =
  r_remove_min_rect

data R_merge1 elt =
   R_merge_6 (Tree1 elt) (Tree1 elt)
 | R_merge_7 (Tree1 elt) (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T
 | R_merge_8 (Tree1 elt) (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T (Tree1 elt) Key elt (Tree1 elt) T (Tree1 elt) (Prod Key elt) Key elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_merge_rect :: ((Tree1 a1) -> (Tree1 a1) -> () -> a2) -> ((Tree1 a1) ->
                (Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T ->
                () -> () -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> (Tree1 
                a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 a1) ->
                Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 a1) -> (Prod 
                Key a1) -> () -> Key -> a1 -> () -> a2) -> (Tree1 a1) ->
                (Tree1 a1) -> (Tree1 a1) -> (R_merge1 a1) -> a2
r_merge_rect f f0 f1 _ _ _ r =
  case r of {
   R_merge_6 x x0 -> f x x0 __;
   R_merge_7 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_merge_8 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __}

r_merge_rec :: ((Tree1 a1) -> (Tree1 a1) -> () -> a2) -> ((Tree1 a1) ->
               (Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> ()
               -> () -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> (Tree1 a1) -> Key
               -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 a1) -> Key -> a1 ->
               (Tree1 a1) -> T -> () -> (Tree1 a1) -> (Prod Key a1) -> () ->
               Key -> a1 -> () -> a2) -> (Tree1 a1) -> (Tree1 a1) -> (Tree1
               a1) -> (R_merge1 a1) -> a2
r_merge_rec =
  r_merge_rect

data R_remove0 elt =
   R_remove_4 (Tree1 elt)
 | R_remove_5 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Tree1 elt) 
 (R_remove0 elt)
 | R_remove_6 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T
 | R_remove_7 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Tree1 elt) 
 (R_remove0 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect0 :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
                  a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
                  (Tree1 a1) -> (R_remove0 a1) -> a2 -> a2) -> ((Tree1 
                  a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () ->
                  () -> () -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1
                  -> (Tree1 a1) -> T -> () -> () -> () -> (Tree1 a1) ->
                  (R_remove0 a1) -> a2 -> a2) -> (Tree1 a1) -> (Tree1 
                  a1) -> (R_remove0 a1) -> a2
r_remove_rect0 x f f0 f1 f2 _ _ r =
  case r of {
   R_remove_4 m -> f m __;
   R_remove_5 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_remove_rect0 x f f0 f1 f2 l _res r1);
   R_remove_6 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_remove_7 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1
      (r_remove_rect0 x f f0 f1 f2 r0 _res r1)}

r_remove_rec0 :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
                 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
                 (Tree1 a1) -> (R_remove0 a1) -> a2 -> a2) -> ((Tree1 
                 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () ->
                 () -> () -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 ->
                 (Tree1 a1) -> T -> () -> () -> () -> (Tree1 a1) ->
                 (R_remove0 a1) -> a2 -> a2) -> (Tree1 a1) -> (Tree1 
                 a1) -> (R_remove0 a1) -> a2
r_remove_rec0 =
  r_remove_rect0

data R_concat1 elt =
   R_concat_6 (Tree1 elt) (Tree1 elt)
 | R_concat_7 (Tree1 elt) (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T
 | R_concat_8 (Tree1 elt) (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) 
 T (Tree1 elt) Key elt (Tree1 elt) T (Tree1 elt) (Prod Key elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_concat_rect :: ((Tree1 a1) -> (Tree1 a1) -> () -> a2) -> ((Tree1 a1) ->
                 (Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T ->
                 () -> () -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> (Tree1 
                 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 
                 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 
                 a1) -> (Prod Key a1) -> () -> a2) -> (Tree1 a1) -> (Tree1
                 a1) -> (Tree1 a1) -> (R_concat1 a1) -> a2
r_concat_rect f f0 f1 _ _ _ r =
  case r of {
   R_concat_6 x x0 -> f x x0 __;
   R_concat_7 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_concat_8 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __}

r_concat_rec :: ((Tree1 a1) -> (Tree1 a1) -> () -> a2) -> ((Tree1 a1) ->
                (Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T ->
                () -> () -> a2) -> ((Tree1 a1) -> (Tree1 a1) -> (Tree1 
                a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 a1) ->
                Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 a1) -> (Prod 
                Key a1) -> () -> a2) -> (Tree1 a1) -> (Tree1 a1) -> (Tree1
                a1) -> (R_concat1 a1) -> a2
r_concat_rec =
  r_concat_rect

data R_split elt =
   R_split_0 (Tree1 elt)
 | R_split_1 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Triple1 elt) 
 (R_split elt) (Tree1 elt) (Option elt) (Tree1 elt)
 | R_split_2 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T
 | R_split_3 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Triple1 elt) 
 (R_split elt) (Tree1 elt) (Option elt) (Tree1 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_split_rect :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
                a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
                (Triple1 a1) -> (R_split a1) -> a2 -> (Tree1 a1) -> (Option
                a1) -> (Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
                a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> a2)
                -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T
                -> () -> () -> () -> (Triple1 a1) -> (R_split a1) -> a2 ->
                (Tree1 a1) -> (Option a1) -> (Tree1 a1) -> () -> a2) ->
                (Tree1 a1) -> (Triple1 a1) -> (R_split a1) -> a2
r_split_rect x f f0 f1 f2 _ _ r =
  case r of {
   R_split_0 m -> f m __;
   R_split_1 m l y d r0 _x _res r1 ll o rl ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_split_rect x f f0 f1 f2 l _res r1)
      ll o rl __;
   R_split_2 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_split_3 m l y d r0 _x _res r1 rl o rr ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_split_rect x f f0 f1 f2 r0 _res r1)
      rl o rr __}

r_split_rec :: S5 -> ((Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
               a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () ->
               (Triple1 a1) -> (R_split a1) -> a2 -> (Tree1 a1) -> (Option
               a1) -> (Tree1 a1) -> () -> a2) -> ((Tree1 a1) -> (Tree1 
               a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> () -> () -> a2)
               -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T
               -> () -> () -> () -> (Triple1 a1) -> (R_split a1) -> a2 ->
               (Tree1 a1) -> (Option a1) -> (Tree1 a1) -> () -> a2) -> (Tree1
               a1) -> (Triple1 a1) -> (R_split a1) -> a2
r_split_rec =
  r_split_rect

data R_map_option elt x =
   R_map_option_0 (Tree1 elt)
 | R_map_option_1 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T x (Tree1 x) 
 (R_map_option elt x) (Tree1 x) (R_map_option elt x)
 | R_map_option_2 (Tree1 elt) (Tree1 elt) Key elt (Tree1 elt) T (Tree1 x) 
 (R_map_option elt x) (Tree1 x) (R_map_option elt x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map_option_rect :: (Key -> a1 -> Option a2) -> ((Tree1 a1) -> () -> a3) ->
                     ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 
                     a1) -> T -> () -> a2 -> () -> (Tree1 a2) ->
                     (R_map_option a1 a2) -> a3 -> (Tree1 a2) ->
                     (R_map_option a1 a2) -> a3 -> a3) -> ((Tree1 a1) ->
                     (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> ()
                     -> (Tree1 a2) -> (R_map_option a1 a2) -> a3 -> (Tree1
                     a2) -> (R_map_option a1 a2) -> a3 -> a3) -> (Tree1 
                     a1) -> (Tree1 a2) -> (R_map_option a1 a2) -> a3
r_map_option_rect f f0 f1 f2 _ _ r =
  case r of {
   R_map_option_0 m -> f0 m __;
   R_map_option_1 m l x d r0 _x d' _res0 r1 _res r2 ->
    f1 m l x d r0 _x __ d' __ _res0 r1
      (r_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect f f0 f1 f2 r0 _res r2);
   R_map_option_2 m l x d r0 _x _res0 r1 _res r2 ->
    f2 m l x d r0 _x __ __ _res0 r1 (r_map_option_rect f f0 f1 f2 l _res0 r1)
      _res r2 (r_map_option_rect f f0 f1 f2 r0 _res r2)}

r_map_option_rec :: (Key -> a1 -> Option a2) -> ((Tree1 a1) -> () -> a3) ->
                    ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 -> (Tree1 
                    a1) -> T -> () -> a2 -> () -> (Tree1 a2) -> (R_map_option
                    a1 a2) -> a3 -> (Tree1 a2) -> (R_map_option a1 a2) -> a3
                    -> a3) -> ((Tree1 a1) -> (Tree1 a1) -> Key -> a1 ->
                    (Tree1 a1) -> T -> () -> () -> (Tree1 a2) ->
                    (R_map_option a1 a2) -> a3 -> (Tree1 a2) -> (R_map_option
                    a1 a2) -> a3 -> a3) -> (Tree1 a1) -> (Tree1 a2) ->
                    (R_map_option a1 a2) -> a3
r_map_option_rec =
  r_map_option_rect

data R_map2_opt elt x0 x =
   R_map2_opt_0 (Tree1 elt) (Tree1 x0)
 | R_map2_opt_1 (Tree1 elt) (Tree1 x0) (Tree1 elt) Key elt (Tree1 elt) 
 T
 | R_map2_opt_2 (Tree1 elt) (Tree1 x0) (Tree1 elt) Key elt (Tree1 elt) 
 T (Tree1 x0) Key x0 (Tree1 x0) T (Tree1 x0) (Option x0) (Tree1 x0) x 
 (Tree1 x) (R_map2_opt elt x0 x) (Tree1 x) (R_map2_opt elt x0 x)
 | R_map2_opt_3 (Tree1 elt) (Tree1 x0) (Tree1 elt) Key elt (Tree1 elt) 
 T (Tree1 x0) Key x0 (Tree1 x0) T (Tree1 x0) (Option x0) (Tree1 x0) (Tree1 x) 
 (R_map2_opt elt x0 x) (Tree1 x) (R_map2_opt elt x0 x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map2_opt_rect :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree1 
                   a1) -> Tree1 a3) -> ((Tree1 a2) -> Tree1 a3) -> ((Tree1
                   a1) -> (Tree1 a2) -> () -> a4) -> ((Tree1 a1) -> (Tree1
                   a2) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () ->
                   () -> a4) -> ((Tree1 a1) -> (Tree1 a2) -> (Tree1 a1) ->
                   Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 a2) -> Key ->
                   a2 -> (Tree1 a2) -> T -> () -> (Tree1 a2) -> (Option 
                   a2) -> (Tree1 a2) -> () -> a3 -> () -> (Tree1 a3) ->
                   (R_map2_opt a1 a2 a3) -> a4 -> (Tree1 a3) -> (R_map2_opt
                   a1 a2 a3) -> a4 -> a4) -> ((Tree1 a1) -> (Tree1 a2) ->
                   (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1
                   a2) -> Key -> a2 -> (Tree1 a2) -> T -> () -> (Tree1 
                   a2) -> (Option a2) -> (Tree1 a2) -> () -> () -> (Tree1 
                   a3) -> (R_map2_opt a1 a2 a3) -> a4 -> (Tree1 a3) ->
                   (R_map2_opt a1 a2 a3) -> a4 -> a4) -> (Tree1 a1) -> (Tree1
                   a2) -> (Tree1 a3) -> (R_map2_opt a1 a2 a3) -> a4
r_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ r =
  case r of {
   R_map2_opt_0 m1 m2 -> f0 m1 m2 __;
   R_map2_opt_1 m1 m2 l1 x1 d1 r1 _x -> f1 m1 m2 l1 x1 d1 r1 _x __ __;
   R_map2_opt_2 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' e _res0
    r0 _res r2 ->
    f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
      _res0 r0 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res
      r2 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2);
   R_map2_opt_3 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' _res0 r0
    _res r2 ->
    f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
      r0 (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
      (r_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)}

r_map2_opt_rec :: (Key -> a1 -> (Option a2) -> Option a3) -> ((Tree1 
                  a1) -> Tree1 a3) -> ((Tree1 a2) -> Tree1 a3) -> ((Tree1 
                  a1) -> (Tree1 a2) -> () -> a4) -> ((Tree1 a1) -> (Tree1 
                  a2) -> (Tree1 a1) -> Key -> a1 -> (Tree1 a1) -> T -> () ->
                  () -> a4) -> ((Tree1 a1) -> (Tree1 a2) -> (Tree1 a1) -> Key
                  -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 a2) -> Key -> a2
                  -> (Tree1 a2) -> T -> () -> (Tree1 a2) -> (Option a2) ->
                  (Tree1 a2) -> () -> a3 -> () -> (Tree1 a3) -> (R_map2_opt
                  a1 a2 a3) -> a4 -> (Tree1 a3) -> (R_map2_opt a1 a2 
                  a3) -> a4 -> a4) -> ((Tree1 a1) -> (Tree1 a2) -> (Tree1 
                  a1) -> Key -> a1 -> (Tree1 a1) -> T -> () -> (Tree1 
                  a2) -> Key -> a2 -> (Tree1 a2) -> T -> () -> (Tree1 
                  a2) -> (Option a2) -> (Tree1 a2) -> () -> () -> (Tree1 
                  a3) -> (R_map2_opt a1 a2 a3) -> a4 -> (Tree1 a3) ->
                  (R_map2_opt a1 a2 a3) -> a4 -> a4) -> (Tree1 a1) -> (Tree1
                  a2) -> (Tree1 a3) -> (R_map2_opt a1 a2 a3) -> a4
r_map2_opt_rec =
  r_map2_opt_rect

fold' :: (Key -> a1 -> a2 -> a2) -> (Tree1 a1) -> a2 -> a2
fold' f s =
  fold6 f (elements5 s)

flatten_e1 :: (Enumeration1 a1) -> List (Prod Key a1)
flatten_e1 e =
  case e of {
   End1 -> Nil;
   More1 x e0 t r -> Cons (Pair x e0) (app (elements5 t) (flatten_e1 r))}

type Bst elt = Tree1 elt
  -- singleton inductive, whose constructor was Bst
  
this1 :: (Bst a1) -> Tree1 a1
this1 b =
  b

type T29 elt = Bst elt

type Key1 = S5

empty7 :: T29 a1
empty7 =
  empty5

is_empty7 :: (T29 a1) -> Bool
is_empty7 m =
  is_empty5 (this1 m)

add10 :: Key1 -> a1 -> (T29 a1) -> T29 a1
add10 x e m =
  add8 x e (this1 m)

remove7 :: Key1 -> (T29 a1) -> T29 a1
remove7 x m =
  remove5 x (this1 m)

mem7 :: Key1 -> (T29 a1) -> Bool
mem7 x m =
  mem5 x (this1 m)

find1 :: Key1 -> (T29 a1) -> Option a1
find1 x m =
  find x (this1 m)

map4 :: (a1 -> a2) -> (T29 a1) -> T29 a2
map4 f m =
  map0 f (this1 m)

mapi1 :: (Key1 -> a1 -> a2) -> (T29 a1) -> T29 a2
mapi1 f m =
  mapi f (this1 m)

map5 :: ((Option a1) -> (Option a2) -> Option a3) -> (T29 a1) -> (T29 
        a2) -> T29 a3
map5 f m m' =
  map2 f (this1 m) (this1 m')

elements7 :: (T29 a1) -> List (Prod Key1 a1)
elements7 m =
  elements5 (this1 m)

cardinal6 :: (T29 a1) -> Nat
cardinal6 m =
  cardinal5 (this1 m)

fold7 :: (Key1 -> a1 -> a2 -> a2) -> (T29 a1) -> a2 -> a2
fold7 f m i =
  fold5 f (this1 m) i

equal7 :: (a1 -> a1 -> Bool) -> (T29 a1) -> (T29 a1) -> Bool
equal7 cmp m m' =
  equal5 cmp (this1 m) (this1 m')

emptyRPMap :: T29 Cash
emptyRPMap =
  empty7

type S7 = Prod IdentChoiceT Person

type S8 = S7

st3 :: S8 -> List Prelude.Integer
st3 x =
  case x of {
   Pair i p -> Cons i (Cons p Nil)}

type T30 = S8

compareList3 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList3 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec3 :: T30 -> T30 -> Sumor Sumbool
compareDec3 x y =
  compareList3 (case x of {
                 Pair i p -> Cons i (Cons p Nil)})
    (case y of {
      Pair i p -> Cons i (Cons p Nil)})

compare25 :: T30 -> T30 -> Compare T30
compare25 x y =
  let {h = compareDec3 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec31 :: T30 -> T30 -> Sumbool
eq_dec31 x y =
  let {h = compareDec3 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type S9 = S7

st4 :: S9 -> List Prelude.Integer
st4 x =
  case x of {
   Pair i p -> Cons i (Cons p Nil)}

type T31 = S9

compareList4 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList4 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec4 :: T31 -> T31 -> Sumor Sumbool
compareDec4 x y =
  compareList4 (case x of {
                 Pair i p -> Cons i (Cons p Nil)})
    (case y of {
      Pair i p -> Cons i (Cons p Nil)})

compare26 :: T31 -> T31 -> Compare T31
compare26 x y =
  let {h = compareDec4 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec32 :: T31 -> T31 -> Sumbool
eq_dec32 x y =
  let {h = compareDec4 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type Key2 = S8

data Tree2 elt =
   Leaf2
 | Node2 (Tree2 elt) Key2 elt (Tree2 elt) T
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

tree_rect0 :: a2 -> ((Tree2 a1) -> a2 -> Key2 -> a1 -> (Tree2 a1) -> a2 -> T
              -> a2) -> (Tree2 a1) -> a2
tree_rect0 f f0 t =
  case t of {
   Leaf2 -> f;
   Node2 t0 k e t1 t2 ->
    f0 t0 (tree_rect0 f f0 t0) k e t1 (tree_rect0 f f0 t1) t2}

tree_rec0 :: a2 -> ((Tree2 a1) -> a2 -> Key2 -> a1 -> (Tree2 a1) -> a2 -> T
             -> a2) -> (Tree2 a1) -> a2
tree_rec0 =
  tree_rect0

height2 :: (Tree2 a1) -> T
height2 m =
  case m of {
   Leaf2 -> _0;
   Node2 _ _ _ _ h -> h}

cardinal7 :: (Tree2 a1) -> Nat
cardinal7 m =
  case m of {
   Leaf2 -> O;
   Node2 l _ _ r _ -> S (add (cardinal7 l) (cardinal7 r))}

empty8 :: Tree2 a1
empty8 =
  Leaf2

is_empty8 :: (Tree2 a1) -> Bool
is_empty8 m =
  case m of {
   Leaf2 -> True;
   Node2 _ _ _ _ _ -> False}

mem8 :: S8 -> (Tree2 a1) -> Bool
mem8 x m =
  case m of {
   Leaf2 -> False;
   Node2 l y _ r _ ->
    case compare25 x y of {
     LT -> mem8 x l;
     EQ -> True;
     GT -> mem8 x r}}

find2 :: S8 -> (Tree2 a1) -> Option a1
find2 x m =
  case m of {
   Leaf2 -> None;
   Node2 l y d r _ ->
    case compare25 x y of {
     LT -> find2 x l;
     EQ -> Some d;
     GT -> find2 x r}}

create2 :: (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> Tree2 a1
create2 l x e r =
  Node2 l x e r (add1 (max0 (height2 l) (height2 r)) _1)

assert_false2 :: (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> Tree2 a1
assert_false2 =
  create2

bal2 :: (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> Tree2 a1
bal2 l x d r =
  let {hl = height2 l} in
  let {hr = height2 r} in
  case gt_le_dec hl (add1 hr _2) of {
   Left ->
    case l of {
     Leaf2 -> assert_false2 l x d r;
     Node2 ll lx ld lr _ ->
      case ge_lt_dec (height2 ll) (height2 lr) of {
       Left -> create2 ll lx ld (create2 lr x d r);
       Right ->
        case lr of {
         Leaf2 -> assert_false2 l x d r;
         Node2 lrl lrx lrd lrr _ ->
          create2 (create2 ll lx ld lrl) lrx lrd (create2 lrr x d r)}}};
   Right ->
    case gt_le_dec hr (add1 hl _2) of {
     Left ->
      case r of {
       Leaf2 -> assert_false2 l x d r;
       Node2 rl rx rd rr _ ->
        case ge_lt_dec (height2 rr) (height2 rl) of {
         Left -> create2 (create2 l x d rl) rx rd rr;
         Right ->
          case rl of {
           Leaf2 -> assert_false2 l x d r;
           Node2 rll rlx rld rlr _ ->
            create2 (create2 l x d rll) rlx rld (create2 rlr rx rd rr)}}};
     Right -> create2 l x d r}}

add11 :: Key2 -> a1 -> (Tree2 a1) -> Tree2 a1
add11 x d m =
  case m of {
   Leaf2 -> Node2 Leaf2 x d Leaf2 _1;
   Node2 l y d' r h ->
    case compare25 x y of {
     LT -> bal2 (add11 x d l) y d' r;
     EQ -> Node2 l y d r h;
     GT -> bal2 l y d' (add11 x d r)}}

remove_min2 :: (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> Prod (Tree2 a1)
               (Prod Key2 a1)
remove_min2 l x d r =
  case l of {
   Leaf2 -> Pair r (Pair x d);
   Node2 ll lx ld lr _ ->
    case remove_min2 ll lx ld lr of {
     Pair l' m -> Pair (bal2 l' x d r) m}}

merge2 :: (Tree2 a1) -> (Tree2 a1) -> Tree2 a1
merge2 s1 s2 =
  case s1 of {
   Leaf2 -> s2;
   Node2 _ _ _ _ _ ->
    case s2 of {
     Leaf2 -> s1;
     Node2 l2 x2 d2 r2 _ ->
      case remove_min2 l2 x2 d2 r2 of {
       Pair s2' p -> case p of {
                      Pair x d -> bal2 s1 x d s2'}}}}

remove8 :: S8 -> (Tree2 a1) -> Tree2 a1
remove8 x m =
  case m of {
   Leaf2 -> Leaf2;
   Node2 l y d r _ ->
    case compare25 x y of {
     LT -> bal2 (remove8 x l) y d r;
     EQ -> merge2 l r;
     GT -> bal2 l y d (remove8 x r)}}

join2 :: (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> Tree2 a1
join2 l =
  case l of {
   Leaf2 -> add11;
   Node2 ll lx ld lr lh -> (\x d ->
    let {
     join_aux r =
       case r of {
        Leaf2 -> add11 x d l;
        Node2 rl rx rd rr rh ->
         case gt_le_dec lh (add1 rh _2) of {
          Left -> bal2 ll lx ld (join2 lr x d r);
          Right ->
           case gt_le_dec rh (add1 lh _2) of {
            Left -> bal2 (join_aux rl) rx rd rr;
            Right -> create2 l x d r}}}}
    in join_aux)}

data Triple2 elt =
   Mktriple2 (Tree2 elt) (Option elt) (Tree2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

t_left2 :: (Triple2 a1) -> Tree2 a1
t_left2 t =
  case t of {
   Mktriple2 t_left5 _ _ -> t_left5}

t_opt0 :: (Triple2 a1) -> Option a1
t_opt0 t =
  case t of {
   Mktriple2 _ t_opt3 _ -> t_opt3}

t_right2 :: (Triple2 a1) -> Tree2 a1
t_right2 t =
  case t of {
   Mktriple2 _ _ t_right5 -> t_right5}

split2 :: S8 -> (Tree2 a1) -> Triple2 a1
split2 x m =
  case m of {
   Leaf2 -> Mktriple2 Leaf2 None Leaf2;
   Node2 l y d r _ ->
    case compare25 x y of {
     LT ->
      case split2 x l of {
       Mktriple2 ll o rl -> Mktriple2 ll o (join2 rl y d r)};
     EQ -> Mktriple2 l (Some d) r;
     GT ->
      case split2 x r of {
       Mktriple2 rl o rr -> Mktriple2 (join2 l y d rl) o rr}}}

concat2 :: (Tree2 a1) -> (Tree2 a1) -> Tree2 a1
concat2 m1 m2 =
  case m1 of {
   Leaf2 -> m2;
   Node2 _ _ _ _ _ ->
    case m2 of {
     Leaf2 -> m1;
     Node2 l2 x2 d2 r2 _ ->
      case remove_min2 l2 x2 d2 r2 of {
       Pair m2' xd -> join2 m1 (fst xd) (snd xd) m2'}}}

elements_aux2 :: (List (Prod Key2 a1)) -> (Tree2 a1) -> List (Prod Key2 a1)
elements_aux2 acc m =
  case m of {
   Leaf2 -> acc;
   Node2 l x d r _ -> elements_aux2 (Cons (Pair x d) (elements_aux2 acc r)) l}

elements8 :: (Tree2 a1) -> List (Prod Key2 a1)
elements8 =
  elements_aux2 Nil

fold8 :: (Key2 -> a1 -> a2 -> a2) -> (Tree2 a1) -> a2 -> a2
fold8 f m a =
  case m of {
   Leaf2 -> a;
   Node2 l x d r _ -> fold8 f r (f x d (fold8 f l a))}

data Enumeration2 elt =
   End2
 | More2 Key2 elt (Tree2 elt) (Enumeration2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

enumeration_rect0 :: a2 -> (Key2 -> a1 -> (Tree2 a1) -> (Enumeration2 
                     a1) -> a2 -> a2) -> (Enumeration2 a1) -> a2
enumeration_rect0 f f0 e =
  case e of {
   End2 -> f;
   More2 k e0 t e1 -> f0 k e0 t e1 (enumeration_rect0 f f0 e1)}

enumeration_rec0 :: a2 -> (Key2 -> a1 -> (Tree2 a1) -> (Enumeration2 
                    a1) -> a2 -> a2) -> (Enumeration2 a1) -> a2
enumeration_rec0 =
  enumeration_rect0

cons2 :: (Tree2 a1) -> (Enumeration2 a1) -> Enumeration2 a1
cons2 m e =
  case m of {
   Leaf2 -> e;
   Node2 l x d r _ -> cons2 l (More2 x d r e)}

equal_more0 :: (a1 -> a1 -> Bool) -> S8 -> a1 -> ((Enumeration2 a1) -> Bool)
               -> (Enumeration2 a1) -> Bool
equal_more0 cmp x1 d1 cont e2 =
  case e2 of {
   End2 -> False;
   More2 x2 d2 r2 e3 ->
    case compare25 x1 x2 of {
     EQ -> case cmp d1 d2 of {
            True -> cont (cons2 r2 e3);
            False -> False};
     _ -> False}}

equal_cont0 :: (a1 -> a1 -> Bool) -> (Tree2 a1) -> ((Enumeration2 a1) ->
               Bool) -> (Enumeration2 a1) -> Bool
equal_cont0 cmp m1 cont e2 =
  case m1 of {
   Leaf2 -> cont e2;
   Node2 l1 x1 d1 r1 _ ->
    equal_cont0 cmp l1 (equal_more0 cmp x1 d1 (equal_cont0 cmp r1 cont)) e2}

equal_end0 :: (Enumeration2 a1) -> Bool
equal_end0 e2 =
  case e2 of {
   End2 -> True;
   More2 _ _ _ _ -> False}

equal8 :: (a1 -> a1 -> Bool) -> (Tree2 a1) -> (Tree2 a1) -> Bool
equal8 cmp m1 m2 =
  equal_cont0 cmp m1 equal_end0 (cons2 m2 End2)

map6 :: (a1 -> a2) -> (Tree2 a1) -> Tree2 a2
map6 f m =
  case m of {
   Leaf2 -> Leaf2;
   Node2 l x d r h -> Node2 (map6 f l) x (f d) (map6 f r) h}

mapi2 :: (Key2 -> a1 -> a2) -> (Tree2 a1) -> Tree2 a2
mapi2 f m =
  case m of {
   Leaf2 -> Leaf2;
   Node2 l x d r h -> Node2 (mapi2 f l) x (f x d) (mapi2 f r) h}

map_option0 :: (Key2 -> a1 -> Option a2) -> (Tree2 a1) -> Tree2 a2
map_option0 f m =
  case m of {
   Leaf2 -> Leaf2;
   Node2 l x d r _ ->
    case f x d of {
     Some d' -> join2 (map_option0 f l) x d' (map_option0 f r);
     None -> concat2 (map_option0 f l) (map_option0 f r)}}

map2_opt0 :: (Key2 -> a1 -> (Option a2) -> Option a3) -> ((Tree2 a1) -> Tree2
             a3) -> ((Tree2 a2) -> Tree2 a3) -> (Tree2 a1) -> (Tree2 
             a2) -> Tree2 a3
map2_opt0 f mapl mapr m1 m2 =
  case m1 of {
   Leaf2 -> mapr m2;
   Node2 l1 x1 d1 r1 _ ->
    case m2 of {
     Leaf2 -> mapl m1;
     Node2 _ _ _ _ _ ->
      case split2 x1 m2 of {
       Mktriple2 l2' o2 r2' ->
        case f x1 d1 o2 of {
         Some e ->
          join2 (map2_opt0 f mapl mapr l1 l2') x1 e
            (map2_opt0 f mapl mapr r1 r2');
         None ->
          concat2 (map2_opt0 f mapl mapr l1 l2')
            (map2_opt0 f mapl mapr r1 r2')}}}}

map7 :: ((Option a1) -> (Option a2) -> Option a3) -> (Tree2 a1) -> (Tree2 
        a2) -> Tree2 a3
map7 f =
  map2_opt0 (\_ d o -> f (Some d) o) (map_option0 (\_ d -> f (Some d) None))
    (map_option0 (\_ d' -> f None (Some d')))

type T32 = S8

eq_dec33 :: S8 -> S8 -> Sumbool
eq_dec33 =
  eq_dec31

lt_dec7 :: S8 -> S8 -> Sumbool
lt_dec7 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare25 x y)

eqb11 :: S8 -> S8 -> Bool
eqb11 x y =
  case eq_dec33 x y of {
   Left -> True;
   Right -> False}

type T33 = S8

eq_dec34 :: S8 -> S8 -> Sumbool
eq_dec34 =
  eq_dec31

lt_dec8 :: S8 -> S8 -> Sumbool
lt_dec8 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare25 x y)

eqb12 :: S8 -> S8 -> Bool
eqb12 x y =
  case eq_dec34 x y of {
   Left -> True;
   Right -> False}

type T34 = S8

eq_dec35 :: S8 -> S8 -> Sumbool
eq_dec35 =
  eq_dec31

lt_dec9 :: S8 -> S8 -> Sumbool
lt_dec9 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare25 x y)

eqb13 :: S8 -> S8 -> Bool
eqb13 x y =
  case eq_dec35 x y of {
   Left -> True;
   Right -> False}

type T35 = S8

eq_dec36 :: S8 -> S8 -> Sumbool
eq_dec36 =
  eq_dec31

lt_dec10 :: S8 -> S8 -> Sumbool
lt_dec10 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare25 x y)

eqb14 :: S8 -> S8 -> Bool
eqb14 x y =
  case eq_dec36 x y of {
   Left -> True;
   Right -> False}

type Key3 = S8

type T36 elt = List (Prod S8 elt)

empty9 :: T36 a1
empty9 =
  Nil

is_empty9 :: (T36 a1) -> Bool
is_empty9 l =
  case l of {
   Nil -> True;
   Cons _ _ -> False}

mem9 :: Key3 -> (T36 a1) -> Bool
mem9 k s =
  case s of {
   Nil -> False;
   Cons p l ->
    case p of {
     Pair k' _ ->
      case compare25 k k' of {
       LT -> False;
       EQ -> True;
       GT -> mem9 k l}}}

data R_mem1 elt =
   R_mem_8 (T36 elt)
 | R_mem_9 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_mem_10 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_mem_11 (T36 elt) S8 elt (List (Prod S8 elt)) Bool (R_mem1 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect1 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
               (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
               a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
               a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
               () -> () -> Bool -> (R_mem1 a1) -> a2 -> a2) -> (T36 a1) ->
               Bool -> (R_mem1 a1) -> a2
r_mem_rect1 k f f0 f1 f2 _ _ r =
  case r of {
   R_mem_8 s -> f s __;
   R_mem_9 s k' _x l -> f0 s k' _x l __ __ __;
   R_mem_10 s k' _x l -> f1 s k' _x l __ __ __;
   R_mem_11 s k' _x l _res r0 ->
    f2 s k' _x l __ __ __ _res r0 (r_mem_rect1 k f f0 f1 f2 l _res r0)}

r_mem_rec1 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
              (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 a1) -> S8
              -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36
              a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
              Bool -> (R_mem1 a1) -> a2 -> a2) -> (T36 a1) -> Bool -> (R_mem1
              a1) -> a2
r_mem_rec1 =
  r_mem_rect1

mem_rect0 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 -> (List
             (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 a1) -> S8 -> a1
             -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
             a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2
             -> a2) -> (T36 a1) -> a2
mem_rect0 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> False;
      Cons p l ->
       case p of {
        Pair k' _ ->
         case compare25 k k' of {
          LT -> False;
          EQ -> True;
          GT -> mem9 k l}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = mem_rect0 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare25 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (mem9 k s)

mem_rec0 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 -> (List
            (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 a1) -> S8 -> a1
            -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
            a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2 ->
            a2) -> (T36 a1) -> a2
mem_rec0 =
  mem_rect0

r_mem_correct0 :: Key3 -> (T36 a1) -> Bool -> R_mem1 a1
r_mem_correct0 k s _res =
  unsafeCoerce mem_rect0 k (\y _ z _ -> eq_rect_r False (R_mem_8 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r False (R_mem_9 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r True (R_mem_10 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (mem9 k y2) (R_mem_11 y y0 y1 y2 (mem9 k y2)
      (y6 (mem9 k y2) __)) z) s _res __

find3 :: Key3 -> (T36 a1) -> Option a1
find3 k s =
  case s of {
   Nil -> None;
   Cons p s' ->
    case p of {
     Pair k' x ->
      case compare25 k k' of {
       LT -> None;
       EQ -> Some x;
       GT -> find3 k s'}}}

data R_find1 elt =
   R_find_8 (T36 elt)
 | R_find_9 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_find_10 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_find_11 (T36 elt) S8 elt (List (Prod S8 elt)) (Option elt) (R_find1 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect1 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
                (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
                a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
                a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
                () -> () -> (Option a1) -> (R_find1 a1) -> a2 -> a2) -> (T36
                a1) -> (Option a1) -> (R_find1 a1) -> a2
r_find_rect1 k f f0 f1 f2 _ _ r =
  case r of {
   R_find_8 s -> f s __;
   R_find_9 s k' x s' -> f0 s k' x s' __ __ __;
   R_find_10 s k' x s' -> f1 s k' x s' __ __ __;
   R_find_11 s k' x s' _res r0 ->
    f2 s k' x s' __ __ __ _res r0 (r_find_rect1 k f f0 f1 f2 s' _res r0)}

r_find_rec1 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
               (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
               a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
               a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
               () -> () -> (Option a1) -> (R_find1 a1) -> a2 -> a2) -> (T36
               a1) -> (Option a1) -> (R_find1 a1) -> a2
r_find_rec1 =
  r_find_rect1

find_rect0 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
              (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 a1) -> S8
              -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36
              a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2
              -> a2) -> (T36 a1) -> a2
find_rect0 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> None;
      Cons p s' ->
       case p of {
        Pair k' x ->
         case compare25 k k' of {
          LT -> None;
          EQ -> Some x;
          GT -> find3 k s'}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = find_rect0 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare25 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (find3 k s)

find_rec0 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 -> (List
             (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 a1) -> S8 -> a1
             -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
             a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2
             -> a2) -> (T36 a1) -> a2
find_rec0 =
  find_rect0

r_find_correct0 :: Key3 -> (T36 a1) -> (Option a1) -> R_find1 a1
r_find_correct0 k s _res =
  unsafeCoerce find_rect0 k (\y _ z _ -> eq_rect_r None (R_find_8 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r None (R_find_9 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r (Some y1) (R_find_10 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (find3 k y2) (R_find_11 y y0 y1 y2 (find3 k y2)
      (y6 (find3 k y2) __)) z) s _res __

add12 :: Key3 -> a1 -> (T36 a1) -> T36 a1
add12 k x s =
  case s of {
   Nil -> Cons (Pair k x) Nil;
   Cons p l ->
    case p of {
     Pair k' y ->
      case compare25 k k' of {
       LT -> Cons (Pair k x) s;
       EQ -> Cons (Pair k x) l;
       GT -> Cons (Pair k' y) (add12 k x l)}}}

data R_add1 elt =
   R_add_8 (T36 elt)
 | R_add_9 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_add_10 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_add_11 (T36 elt) S8 elt (List (Prod S8 elt)) (T36 elt) (R_add1 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect1 :: Key3 -> a1 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1
               -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
               a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
               a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
               () -> () -> (T36 a1) -> (R_add1 a1) -> a2 -> a2) -> (T36 
               a1) -> (T36 a1) -> (R_add1 a1) -> a2
r_add_rect1 k x f f0 f1 f2 _ _ r =
  case r of {
   R_add_8 s -> f s __;
   R_add_9 s k' y l -> f0 s k' y l __ __ __;
   R_add_10 s k' y l -> f1 s k' y l __ __ __;
   R_add_11 s k' y l _res r0 ->
    f2 s k' y l __ __ __ _res r0 (r_add_rect1 k x f f0 f1 f2 l _res r0)}

r_add_rec1 :: Key3 -> a1 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1
              -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
              a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2)
              -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () ->
              () -> (T36 a1) -> (R_add1 a1) -> a2 -> a2) -> (T36 a1) -> (T36
              a1) -> (R_add1 a1) -> a2
r_add_rec1 =
  r_add_rect1

add_rect0 :: Key3 -> a1 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
             (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 a1) -> S8
             -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36
             a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2
             -> a2) -> (T36 a1) -> a2
add_rect0 k x f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Cons (Pair k x) Nil;
      Cons p l ->
       case p of {
        Pair k' y ->
         case compare25 k k' of {
          LT -> Cons (Pair k x) s;
          EQ -> Cons (Pair k x) l;
          GT -> Cons (Pair k' y) (add12 k x l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = add_rect0 k x f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare25 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (add12 k x s)

add_rec0 :: Key3 -> a1 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
            (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 a1) -> S8
            -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36
            a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2 ->
            a2) -> (T36 a1) -> a2
add_rec0 =
  add_rect0

r_add_correct0 :: Key3 -> a1 -> (T36 a1) -> (T36 a1) -> R_add1 a1
r_add_correct0 k x s _res =
  add_rect0 k x (\y _ z _ -> eq_rect_r (Cons (Pair k x) Nil) (R_add_8 y) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y) (R_add_9 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y2) (R_add_10 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (add12 k x y2)) (R_add_11 y y0 y1 y2
      (add12 k x y2) (y6 (add12 k x y2) __)) z) s _res __

remove9 :: Key3 -> (T36 a1) -> T36 a1
remove9 k s =
  case s of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k' x ->
      case compare25 k k' of {
       LT -> s;
       EQ -> l;
       GT -> Cons (Pair k' x) (remove9 k l)}}}

data R_remove1 elt =
   R_remove_8 (T36 elt)
 | R_remove_9 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_remove_10 (T36 elt) S8 elt (List (Prod S8 elt))
 | R_remove_11 (T36 elt) S8 elt (List (Prod S8 elt)) (T36 elt) (R_remove1
                                                               elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect1 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
                  (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
                  a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
                  a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> ()
                  -> () -> () -> (T36 a1) -> (R_remove1 a1) -> a2 -> a2) ->
                  (T36 a1) -> (T36 a1) -> (R_remove1 a1) -> a2
r_remove_rect1 k f f0 f1 f2 _ _ r =
  case r of {
   R_remove_8 s -> f s __;
   R_remove_9 s k' x l -> f0 s k' x l __ __ __;
   R_remove_10 s k' x l -> f1 s k' x l __ __ __;
   R_remove_11 s k' x l _res r0 ->
    f2 s k' x l __ __ __ _res r0 (r_remove_rect1 k f f0 f1 f2 l _res r0)}

r_remove_rec1 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
                 (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
                 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
                 a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
                 () -> () -> (T36 a1) -> (R_remove1 a1) -> a2 -> a2) -> (T36
                 a1) -> (T36 a1) -> (R_remove1 a1) -> a2
r_remove_rec1 =
  r_remove_rect1

remove_rect0 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
                (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
                a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
                a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
                () -> () -> a2 -> a2) -> (T36 a1) -> a2
remove_rect0 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Nil;
      Cons p l ->
       case p of {
        Pair k' x ->
         case compare25 k k' of {
          LT -> s;
          EQ -> l;
          GT -> Cons (Pair k' x) (remove9 k l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = remove_rect0 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare25 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (remove9 k s)

remove_rec0 :: Key3 -> ((T36 a1) -> () -> a2) -> ((T36 a1) -> S8 -> a1 ->
               (List (Prod S8 a1)) -> () -> () -> () -> a2) -> ((T36 
               a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () ->
               a2) -> ((T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
               () -> () -> a2 -> a2) -> (T36 a1) -> a2
remove_rec0 =
  remove_rect0

r_remove_correct0 :: Key3 -> (T36 a1) -> (T36 a1) -> R_remove1 a1
r_remove_correct0 k s _res =
  unsafeCoerce remove_rect0 k (\y _ z _ -> eq_rect_r Nil (R_remove_8 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y (R_remove_9 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y2 (R_remove_10 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (remove9 k y2)) (R_remove_11 y y0 y1 y2
      (remove9 k y2) (y6 (remove9 k y2) __)) z) s _res __

elements9 :: (T36 a1) -> T36 a1
elements9 m =
  m

fold9 :: (Key3 -> a1 -> a2 -> a2) -> (T36 a1) -> a2 -> a2
fold9 f m acc =
  case m of {
   Nil -> acc;
   Cons p m' -> case p of {
                 Pair k e -> fold9 f m' (f k e acc)}}

data R_fold0 elt a =
   R_fold_2 (T36 elt) a
 | R_fold_3 (T36 elt) a S8 elt (List (Prod S8 elt)) a (R_fold0 elt a)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_fold_rect0 :: (Key3 -> a1 -> a2 -> a2) -> ((T36 a1) -> a2 -> () -> a3) ->
                ((T36 a1) -> a2 -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
                a2 -> (R_fold0 a1 a2) -> a3 -> a3) -> (T36 a1) -> a2 -> a2 ->
                (R_fold0 a1 a2) -> a3
r_fold_rect0 f f0 f1 _ _ _ r =
  case r of {
   R_fold_2 m acc -> f0 m acc __;
   R_fold_3 m acc k e m' _res r0 ->
    f1 m acc k e m' __ _res r0 (r_fold_rect0 f f0 f1 m' (f k e acc) _res r0)}

r_fold_rec0 :: (Key3 -> a1 -> a2 -> a2) -> ((T36 a1) -> a2 -> () -> a3) ->
               ((T36 a1) -> a2 -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> a2
               -> (R_fold0 a1 a2) -> a3 -> a3) -> (T36 a1) -> a2 -> a2 ->
               (R_fold0 a1 a2) -> a3
r_fold_rec0 =
  r_fold_rect0

fold_rect0 :: (Key3 -> a1 -> a2 -> a2) -> ((T36 a1) -> a2 -> () -> a3) ->
              ((T36 a1) -> a2 -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> a3
              -> a3) -> (T36 a1) -> a2 -> a3
fold_rect0 f1 f0 f m acc =
  eq_rect_r
    (case m of {
      Nil -> acc;
      Cons p m' -> case p of {
                    Pair k e -> fold9 f1 m' (f1 k e acc)}})
    (let {f2 = f0 m acc} in
     let {f3 = f m acc} in
     case m of {
      Nil -> f2 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f4 = f3 t0 e l __} in
         let {hrec = fold_rect0 f1 f0 f l (f1 t0 e acc)} in f4 hrec}})
    (fold9 f1 m acc)

fold_rec0 :: (Key3 -> a1 -> a2 -> a2) -> ((T36 a1) -> a2 -> () -> a3) ->
             ((T36 a1) -> a2 -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> a3
             -> a3) -> (T36 a1) -> a2 -> a3
fold_rec0 =
  fold_rect0

r_fold_correct0 :: (Key3 -> a1 -> a2 -> a2) -> (T36 a1) -> a2 -> a2 ->
                   R_fold0 a1 a2
r_fold_correct0 f m acc _res =
  fold_rect0 f (\y y0 _ z _ -> eq_rect_r y0 (R_fold_2 y y0) z)
    (\y y0 y1 y2 y3 _ y5 z _ ->
    eq_rect_r (fold9 f y3 (f y1 y2 y0)) (R_fold_3 y y0 y1 y2 y3
      (fold9 f y3 (f y1 y2 y0)) (y5 (fold9 f y3 (f y1 y2 y0)) __)) z) m acc
    _res __

equal9 :: (a1 -> a1 -> Bool) -> (T36 a1) -> (T36 a1) -> Bool
equal9 cmp m m' =
  case m of {
   Nil -> case m' of {
           Nil -> True;
           Cons _ _ -> False};
   Cons p l ->
    case p of {
     Pair x e ->
      case m' of {
       Nil -> False;
       Cons p0 l' ->
        case p0 of {
         Pair x' e' ->
          case compare25 x x' of {
           EQ -> andb (cmp e e') (equal9 cmp l l');
           _ -> False}}}}}

data R_equal0 elt =
   R_equal_4 (T36 elt) (T36 elt)
 | R_equal_5 (T36 elt) (T36 elt) S8 elt (List (Prod S8 elt)) S8 elt (List
                                                                    (Prod 
                                                                    S8 
                                                                    elt)) 
 Bool (R_equal0 elt)
 | R_equal_6 (T36 elt) (T36 elt) S8 elt (List (Prod S8 elt)) S8 elt (List
                                                                    (Prod 
                                                                    S8 
                                                                    elt)) 
 (Compare S8)
 | R_equal_7 (T36 elt) (T36 elt) (T36 elt) (T36 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_equal_rect0 :: (a1 -> a1 -> Bool) -> ((T36 a1) -> (T36 a1) -> () -> () ->
                 a2) -> ((T36 a1) -> (T36 a1) -> S8 -> a1 -> (List
                 (Prod S8 a1)) -> () -> S8 -> a1 -> (List (Prod S8 a1)) -> ()
                 -> () -> () -> Bool -> (R_equal0 a1) -> a2 -> a2) -> ((T36
                 a1) -> (T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
                 S8 -> a1 -> (List (Prod S8 a1)) -> () -> (Compare S8) -> ()
                 -> () -> a2) -> ((T36 a1) -> (T36 a1) -> (T36 a1) -> () ->
                 (T36 a1) -> () -> () -> a2) -> (T36 a1) -> (T36 a1) -> Bool
                 -> (R_equal0 a1) -> a2
r_equal_rect0 cmp f f0 f1 f2 _ _ _ r =
  case r of {
   R_equal_4 m m' -> f m m' __ __;
   R_equal_5 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (r_equal_rect0 cmp f f0 f1 f2 l l' _res r0);
   R_equal_6 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   R_equal_7 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

r_equal_rec0 :: (a1 -> a1 -> Bool) -> ((T36 a1) -> (T36 a1) -> () -> () ->
                a2) -> ((T36 a1) -> (T36 a1) -> S8 -> a1 -> (List
                (Prod S8 a1)) -> () -> S8 -> a1 -> (List (Prod S8 a1)) -> ()
                -> () -> () -> Bool -> (R_equal0 a1) -> a2 -> a2) -> ((T36
                a1) -> (T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
                S8 -> a1 -> (List (Prod S8 a1)) -> () -> (Compare S8) -> ()
                -> () -> a2) -> ((T36 a1) -> (T36 a1) -> (T36 a1) -> () ->
                (T36 a1) -> () -> () -> a2) -> (T36 a1) -> (T36 a1) -> Bool
                -> (R_equal0 a1) -> a2
r_equal_rec0 =
  r_equal_rect0

equal_rect0 :: (a1 -> a1 -> Bool) -> ((T36 a1) -> (T36 a1) -> () -> () -> a2)
               -> ((T36 a1) -> (T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) ->
               () -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2
               -> a2) -> ((T36 a1) -> (T36 a1) -> S8 -> a1 -> (List
               (Prod S8 a1)) -> () -> S8 -> a1 -> (List (Prod S8 a1)) -> ()
               -> (Compare S8) -> () -> () -> a2) -> ((T36 a1) -> (T36 
               a1) -> (T36 a1) -> () -> (T36 a1) -> () -> () -> a2) -> (T36
               a1) -> (T36 a1) -> a2
equal_rect0 cmp f2 f1 f0 f m m' =
  eq_rect_r
    (case m of {
      Nil -> case m' of {
              Nil -> True;
              Cons _ _ -> False};
      Cons p l ->
       case p of {
        Pair x e ->
         case m' of {
          Nil -> False;
          Cons p0 l' ->
           case p0 of {
            Pair x' e' ->
             case compare25 x x' of {
              EQ -> andb (cmp e e') (equal9 cmp l l');
              _ -> False}}}}})
    (let {f3 = f2 m m'} in
     let {f4 = f1 m m'} in
     let {f5 = f0 m m'} in
     let {f6 = f m m'} in
     let {f7 = f6 m __} in
     let {f8 = f7 m' __} in
     case m of {
      Nil ->
       let {f9 = f3 __} in case m' of {
                            Nil -> f9 __;
                            Cons _ _ -> f8 __};
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case m' of {
          Nil -> f8 __;
          Cons p0 l0 ->
           case p0 of {
            Pair t1 e0 ->
             let {f11 = f9 t1 e0 l0 __} in
             let {f12 = let {_x = compare25 t0 t1} in f11 _x __} in
             let {f13 = f10 t1 e0 l0 __} in
             let {
              f14 = \_ _ ->
               let {hrec = equal_rect0 cmp f2 f1 f0 f l l0} in f13 __ __ hrec}
             in
             case compare25 t0 t1 of {
              EQ -> f14 __ __;
              _ -> f12 __}}}}}) (equal9 cmp m m')

equal_rec0 :: (a1 -> a1 -> Bool) -> ((T36 a1) -> (T36 a1) -> () -> () -> a2)
              -> ((T36 a1) -> (T36 a1) -> S8 -> a1 -> (List (Prod S8 a1)) ->
              () -> S8 -> a1 -> (List (Prod S8 a1)) -> () -> () -> () -> a2
              -> a2) -> ((T36 a1) -> (T36 a1) -> S8 -> a1 -> (List
              (Prod S8 a1)) -> () -> S8 -> a1 -> (List (Prod S8 a1)) -> () ->
              (Compare S8) -> () -> () -> a2) -> ((T36 a1) -> (T36 a1) ->
              (T36 a1) -> () -> (T36 a1) -> () -> () -> a2) -> (T36 a1) ->
              (T36 a1) -> a2
equal_rec0 =
  equal_rect0

r_equal_correct0 :: (a1 -> a1 -> Bool) -> (T36 a1) -> (T36 a1) -> Bool ->
                    R_equal0 a1
r_equal_correct0 cmp m m' _res =
  equal_rect0 cmp (\y y0 _ _ z _ -> eq_rect_r True (R_equal_4 y y0) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ ->
    eq_rect_r (andb (cmp y2 y6) (equal9 cmp y3 y7)) (R_equal_5 y y0 y1 y2 y3
      y5 y6 y7 (equal9 cmp y3 y7) (y11 (equal9 cmp y3 y7) __)) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ ->
    eq_rect_r False (R_equal_6 y y0 y1 y2 y3 y5 y6 y7 y9) z)
    (\y y0 y1 _ y3 _ _ z _ -> eq_rect_r False (R_equal_7 y y0 y1 y3) z) m m'
    _res __

map8 :: (a1 -> a2) -> (T36 a1) -> T36 a2
map8 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f e)) (map8 f m')}}

mapi3 :: (Key3 -> a1 -> a2) -> (T36 a1) -> T36 a2
mapi3 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f k e)) (mapi3 f m')}}

option_cons0 :: Key3 -> (Option a1) -> (List (Prod Key3 a1)) -> List
                (Prod Key3 a1)
option_cons0 k o l =
  case o of {
   Some e -> Cons (Pair k e) l;
   None -> l}

map2_l0 :: ((Option a1) -> (Option a2) -> Option a3) -> (T36 a1) -> T36 a3
map2_l0 f m =
  case m of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k e -> option_cons0 k (f (Some e) None) (map2_l0 f l)}}

map2_r0 :: ((Option a1) -> (Option a2) -> Option a3) -> (T36 a2) -> T36 a3
map2_r0 f m' =
  case m' of {
   Nil -> Nil;
   Cons p l' ->
    case p of {
     Pair k e' -> option_cons0 k (f None (Some e')) (map2_r0 f l')}}

map9 :: ((Option a1) -> (Option a2) -> Option a3) -> (T36 a1) -> (T36 
        a2) -> T36 a3
map9 f m =
  case m of {
   Nil -> map2_r0 f;
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       map2_aux m' =
         case m' of {
          Nil -> map2_l0 f m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare25 k k' of {
              LT -> option_cons0 k (f (Some e) None) (map9 f l m');
              EQ -> option_cons0 k (f (Some e) (Some e')) (map9 f l l');
              GT -> option_cons0 k' (f None (Some e')) (map2_aux l')}}}}
      in map2_aux}}

combine0 :: (T36 a1) -> (T36 a2) -> T36 (Prod (Option a1) (Option a2))
combine0 m =
  case m of {
   Nil -> map8 (\e' -> Pair None (Some e'));
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       combine_aux m' =
         case m' of {
          Nil -> map8 (\e0 -> Pair (Some e0) None) m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare25 k k' of {
              LT -> Cons (Pair k (Pair (Some e) None)) (combine0 l m');
              EQ -> Cons (Pair k (Pair (Some e) (Some e'))) (combine0 l l');
              GT -> Cons (Pair k' (Pair None (Some e'))) (combine_aux l')}}}}
      in combine_aux}}

fold_right_pair0 :: (a1 -> a2 -> a3 -> a3) -> (List (Prod a1 a2)) -> a3 -> a3
fold_right_pair0 f l i =
  fold_right (\p -> f (fst p) (snd p)) i l

map2_alt0 :: ((Option a1) -> (Option a2) -> Option a3) -> (T36 a1) -> (T36
             a2) -> List (Prod Key3 a3)
map2_alt0 f m m' =
  let {m0 = combine0 m m'} in
  let {m1 = map8 (\p -> f (fst p) (snd p)) m0} in
  fold_right_pair0 option_cons0 m1 Nil

at_least_one0 :: (Option a1) -> (Option a2) -> Option
                 (Prod (Option a1) (Option a2))
at_least_one0 o o' =
  case o of {
   Some _ -> Some (Pair o o');
   None -> case o' of {
            Some _ -> Some (Pair o o');
            None -> None}}

at_least_one_then_f0 :: ((Option a1) -> (Option a2) -> Option a3) -> (Option
                        a1) -> (Option a2) -> Option a3
at_least_one_then_f0 f o o' =
  case o of {
   Some _ -> f o o';
   None -> case o' of {
            Some _ -> f o o';
            None -> None}}

data R_mem2 elt =
   R_mem_12 (Tree2 elt)
 | R_mem_13 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T Bool (R_mem2 elt)
 | R_mem_14 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T
 | R_mem_15 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T Bool (R_mem2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect2 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
               a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () -> Bool
               -> (R_mem2 a1) -> a2 -> a2) -> ((Tree2 a1) -> (Tree2 a1) ->
               Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () -> a2) ->
               ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T ->
               () -> () -> () -> Bool -> (R_mem2 a1) -> a2 -> a2) -> (Tree2
               a1) -> Bool -> (R_mem2 a1) -> a2
r_mem_rect2 x f f0 f1 f2 _ _ r =
  case r of {
   R_mem_12 m -> f m __;
   R_mem_13 m l y _x r0 _x0 _res r1 ->
    f0 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect2 x f f0 f1 f2 l _res r1);
   R_mem_14 m l y _x r0 _x0 -> f1 m l y _x r0 _x0 __ __ __;
   R_mem_15 m l y _x r0 _x0 _res r1 ->
    f2 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect2 x f f0 f1 f2 r0 _res r1)}

r_mem_rec2 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
              a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () -> Bool
              -> (R_mem2 a1) -> a2 -> a2) -> ((Tree2 a1) -> (Tree2 a1) ->
              Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T ->
              () -> () -> () -> Bool -> (R_mem2 a1) -> a2 -> a2) -> (Tree2
              a1) -> Bool -> (R_mem2 a1) -> a2
r_mem_rec2 =
  r_mem_rect2

data R_find2 elt =
   R_find_12 (Tree2 elt)
 | R_find_13 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Option elt) 
 (R_find2 elt)
 | R_find_14 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T
 | R_find_15 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Option elt) 
 (R_find2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect2 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
                a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
                (Option a1) -> (R_find2 a1) -> a2 -> a2) -> ((Tree2 a1) ->
                (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> ()
                -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2
                a1) -> T -> () -> () -> () -> (Option a1) -> (R_find2 
                a1) -> a2 -> a2) -> (Tree2 a1) -> (Option a1) -> (R_find2 
                a1) -> a2
r_find_rect2 x f f0 f1 f2 _ _ r =
  case r of {
   R_find_12 m -> f m __;
   R_find_13 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_find_rect2 x f f0 f1 f2 l _res r1);
   R_find_14 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_find_15 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_find_rect2 x f f0 f1 f2 r0 _res r1)}

r_find_rec2 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
               a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
               (Option a1) -> (R_find2 a1) -> a2 -> a2) -> ((Tree2 a1) ->
               (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2
               a1) -> T -> () -> () -> () -> (Option a1) -> (R_find2 
               a1) -> a2 -> a2) -> (Tree2 a1) -> (Option a1) -> (R_find2 
               a1) -> a2
r_find_rec2 =
  r_find_rect2

data R_bal2 elt =
   R_bal_27 (Tree2 elt) Key2 elt (Tree2 elt)
 | R_bal_28 (Tree2 elt) Key2 elt (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T
 | R_bal_29 (Tree2 elt) Key2 elt (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T
 | R_bal_30 (Tree2 elt) Key2 elt (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T (Tree2 elt) Key2 elt (Tree2 elt) T
 | R_bal_31 (Tree2 elt) Key2 elt (Tree2 elt)
 | R_bal_32 (Tree2 elt) Key2 elt (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T
 | R_bal_33 (Tree2 elt) Key2 elt (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T
 | R_bal_34 (Tree2 elt) Key2 elt (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T (Tree2 elt) Key2 elt (Tree2 elt) T
 | R_bal_35 (Tree2 elt) Key2 elt (Tree2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_bal_rect0 :: ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> () -> () ->
               a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> () ->
               (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> ()
               -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () ->
               () -> () -> a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 
               a1) -> () -> () -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 
               a1) -> T -> () -> () -> () -> (Tree2 a1) -> Key2 -> a1 ->
               (Tree2 a1) -> T -> () -> a2) -> ((Tree2 a1) -> Key2 -> a1 ->
               (Tree2 a1) -> () -> () -> () -> () -> () -> a2) -> ((Tree2 
               a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> () -> () -> () ->
               (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> ()
               -> () -> () -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T ->
               () -> () -> () -> () -> a2) -> ((Tree2 a1) -> Key2 -> a1 ->
               (Tree2 a1) -> () -> () -> () -> () -> (Tree2 a1) -> Key2 -> a1
               -> (Tree2 a1) -> T -> () -> () -> () -> (Tree2 a1) -> Key2 ->
               a1 -> (Tree2 a1) -> T -> () -> a2) -> ((Tree2 a1) -> Key2 ->
               a1 -> (Tree2 a1) -> () -> () -> () -> () -> a2) -> (Tree2 
               a1) -> Key2 -> a1 -> (Tree2 a1) -> (Tree2 a1) -> (R_bal2 
               a1) -> a2
r_bal_rect0 f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ r =
  case r of {
   R_bal_27 x x0 x1 x2 -> f x x0 x1 x2 __ __ __;
   R_bal_28 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_29 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_30 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_31 x x0 x1 x2 -> f3 x x0 x1 x2 __ __ __ __ __;
   R_bal_32 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_33 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_34 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_35 x x0 x1 x2 -> f7 x x0 x1 x2 __ __ __ __}

r_bal_rec0 :: ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> () -> () ->
              a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> () ->
              (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> ()
              -> a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> ()
              -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () ->
              () -> () -> a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 
              a1) -> () -> () -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T
              -> () -> () -> () -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 
              a1) -> T -> () -> a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2
              a1) -> () -> () -> () -> () -> () -> a2) -> ((Tree2 a1) -> Key2
              -> a1 -> (Tree2 a1) -> () -> () -> () -> () -> (Tree2 a1) ->
              Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> () -> () -> ()
              -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () ->
              () -> () -> a2) -> ((Tree2 a1) -> Key2 -> a1 -> (Tree2 
              a1) -> () -> () -> () -> () -> (Tree2 a1) -> Key2 -> a1 ->
              (Tree2 a1) -> T -> () -> () -> () -> (Tree2 a1) -> Key2 -> a1
              -> (Tree2 a1) -> T -> () -> a2) -> ((Tree2 a1) -> Key2 -> a1 ->
              (Tree2 a1) -> () -> () -> () -> () -> a2) -> (Tree2 a1) -> Key2
              -> a1 -> (Tree2 a1) -> (Tree2 a1) -> (R_bal2 a1) -> a2
r_bal_rec0 =
  r_bal_rect0

data R_add2 elt =
   R_add_12 (Tree2 elt)
 | R_add_13 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Tree2 elt) 
 (R_add2 elt)
 | R_add_14 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T
 | R_add_15 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Tree2 elt) 
 (R_add2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect2 :: Key2 -> a1 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) ->
               (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> ()
               -> (Tree2 a1) -> (R_add2 a1) -> a2 -> a2) -> ((Tree2 a1) ->
               (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2
               a1) -> T -> () -> () -> () -> (Tree2 a1) -> (R_add2 a1) -> a2
               -> a2) -> (Tree2 a1) -> (Tree2 a1) -> (R_add2 a1) -> a2
r_add_rect2 x d f f0 f1 f2 _ _ r =
  case r of {
   R_add_12 m -> f m __;
   R_add_13 m l y d' r0 h _res r1 ->
    f0 m l y d' r0 h __ __ __ _res r1 (r_add_rect2 x d f f0 f1 f2 l _res r1);
   R_add_14 m l y d' r0 h -> f1 m l y d' r0 h __ __ __;
   R_add_15 m l y d' r0 h _res r1 ->
    f2 m l y d' r0 h __ __ __ _res r1 (r_add_rect2 x d f f0 f1 f2 r0 _res r1)}

r_add_rec2 :: Key2 -> a1 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2
              a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
              (Tree2 a1) -> (R_add2 a1) -> a2 -> a2) -> ((Tree2 a1) -> (Tree2
              a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () -> a2)
              -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T
              -> () -> () -> () -> (Tree2 a1) -> (R_add2 a1) -> a2 -> a2) ->
              (Tree2 a1) -> (Tree2 a1) -> (R_add2 a1) -> a2
r_add_rec2 =
  r_add_rect2

data R_remove_min2 elt =
   R_remove_min_6 (Tree2 elt) Key2 elt (Tree2 elt)
 | R_remove_min_7 (Tree2 elt) Key2 elt (Tree2 elt) (Tree2 elt) Key2 elt 
 (Tree2 elt) T (Prod (Tree2 elt) (Prod Key2 elt)) (R_remove_min2 elt) 
 (Tree2 elt) (Prod Key2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_min_rect0 :: ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> a2) ->
                      ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> (Tree2 
                      a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Prod
                      (Tree2 a1) (Prod Key2 a1)) -> (R_remove_min2 a1) -> a2
                      -> (Tree2 a1) -> (Prod Key2 a1) -> () -> a2) -> (Tree2
                      a1) -> Key2 -> a1 -> (Tree2 a1) -> (Prod (Tree2 a1)
                      (Prod Key2 a1)) -> (R_remove_min2 a1) -> a2
r_remove_min_rect0 f f0 _ _ _ _ _ r =
  case r of {
   R_remove_min_6 l x d r0 -> f l x d r0 __;
   R_remove_min_7 l x d r0 ll lx ld lr _x _res r1 l' m ->
    f0 l x d r0 ll lx ld lr _x __ _res r1
      (r_remove_min_rect0 f f0 ll lx ld lr _res r1) l' m __}

r_remove_min_rec0 :: ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> () -> a2) ->
                     ((Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> (Tree2 
                     a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Prod
                     (Tree2 a1) (Prod Key2 a1)) -> (R_remove_min2 a1) -> a2
                     -> (Tree2 a1) -> (Prod Key2 a1) -> () -> a2) -> (Tree2
                     a1) -> Key2 -> a1 -> (Tree2 a1) -> (Prod (Tree2 a1)
                     (Prod Key2 a1)) -> (R_remove_min2 a1) -> a2
r_remove_min_rec0 =
  r_remove_min_rect0

data R_merge2 elt =
   R_merge_9 (Tree2 elt) (Tree2 elt)
 | R_merge_10 (Tree2 elt) (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T
 | R_merge_11 (Tree2 elt) (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T (Tree2 elt) Key2 elt (Tree2 elt) T (Tree2 elt) (Prod Key2 elt) Key2 
 elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_merge_rect0 :: ((Tree2 a1) -> (Tree2 a1) -> () -> a2) -> ((Tree2 a1) ->
                 (Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T ->
                 () -> () -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> (Tree2 
                 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                 a1) -> (Prod Key2 a1) -> () -> Key2 -> a1 -> () -> a2) ->
                 (Tree2 a1) -> (Tree2 a1) -> (Tree2 a1) -> (R_merge2 
                 a1) -> a2
r_merge_rect0 f f0 f1 _ _ _ r =
  case r of {
   R_merge_9 x x0 -> f x x0 __;
   R_merge_10 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_merge_11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __}

r_merge_rec0 :: ((Tree2 a1) -> (Tree2 a1) -> () -> a2) -> ((Tree2 a1) ->
                (Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T ->
                () -> () -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> (Tree2 
                a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                a1) -> (Prod Key2 a1) -> () -> Key2 -> a1 -> () -> a2) ->
                (Tree2 a1) -> (Tree2 a1) -> (Tree2 a1) -> (R_merge2 a1) -> a2
r_merge_rec0 =
  r_merge_rect0

data R_remove2 elt =
   R_remove_12 (Tree2 elt)
 | R_remove_13 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Tree2 elt) 
 (R_remove2 elt)
 | R_remove_14 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T
 | R_remove_15 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Tree2 elt) 
 (R_remove2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect2 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
                  a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
                  (Tree2 a1) -> (R_remove2 a1) -> a2 -> a2) -> ((Tree2 
                  a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () ->
                  () -> () -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1
                  -> (Tree2 a1) -> T -> () -> () -> () -> (Tree2 a1) ->
                  (R_remove2 a1) -> a2 -> a2) -> (Tree2 a1) -> (Tree2 
                  a1) -> (R_remove2 a1) -> a2
r_remove_rect2 x f f0 f1 f2 _ _ r =
  case r of {
   R_remove_12 m -> f m __;
   R_remove_13 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_remove_rect2 x f f0 f1 f2 l _res r1);
   R_remove_14 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_remove_15 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1
      (r_remove_rect2 x f f0 f1 f2 r0 _res r1)}

r_remove_rec2 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
                 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
                 (Tree2 a1) -> (R_remove2 a1) -> a2 -> a2) -> ((Tree2 
                 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () ->
                 () -> () -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1
                 -> (Tree2 a1) -> T -> () -> () -> () -> (Tree2 a1) ->
                 (R_remove2 a1) -> a2 -> a2) -> (Tree2 a1) -> (Tree2 
                 a1) -> (R_remove2 a1) -> a2
r_remove_rec2 =
  r_remove_rect2

data R_concat2 elt =
   R_concat_9 (Tree2 elt) (Tree2 elt)
 | R_concat_10 (Tree2 elt) (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T
 | R_concat_11 (Tree2 elt) (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) 
 T (Tree2 elt) Key2 elt (Tree2 elt) T (Tree2 elt) (Prod Key2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_concat_rect0 :: ((Tree2 a1) -> (Tree2 a1) -> () -> a2) -> ((Tree2 a1) ->
                  (Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T
                  -> () -> () -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> (Tree2
                  a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                  a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                  a1) -> (Prod Key2 a1) -> () -> a2) -> (Tree2 a1) -> (Tree2
                  a1) -> (Tree2 a1) -> (R_concat2 a1) -> a2
r_concat_rect0 f f0 f1 _ _ _ r =
  case r of {
   R_concat_9 x x0 -> f x x0 __;
   R_concat_10 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_concat_11 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __}

r_concat_rec0 :: ((Tree2 a1) -> (Tree2 a1) -> () -> a2) -> ((Tree2 a1) ->
                 (Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T ->
                 () -> () -> a2) -> ((Tree2 a1) -> (Tree2 a1) -> (Tree2 
                 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                 a1) -> (Prod Key2 a1) -> () -> a2) -> (Tree2 a1) -> (Tree2
                 a1) -> (Tree2 a1) -> (R_concat2 a1) -> a2
r_concat_rec0 =
  r_concat_rect0

data R_split0 elt =
   R_split_4 (Tree2 elt)
 | R_split_5 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Triple2 elt) 
 (R_split0 elt) (Tree2 elt) (Option elt) (Tree2 elt)
 | R_split_6 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T
 | R_split_7 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Triple2 elt) 
 (R_split0 elt) (Tree2 elt) (Option elt) (Tree2 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_split_rect0 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
                 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
                 (Triple2 a1) -> (R_split0 a1) -> a2 -> (Tree2 a1) -> (Option
                 a1) -> (Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
                 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
                 a2) -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 
                 a1) -> T -> () -> () -> () -> (Triple2 a1) -> (R_split0 
                 a1) -> a2 -> (Tree2 a1) -> (Option a1) -> (Tree2 a1) -> ()
                 -> a2) -> (Tree2 a1) -> (Triple2 a1) -> (R_split0 a1) -> a2
r_split_rect0 x f f0 f1 f2 _ _ r =
  case r of {
   R_split_4 m -> f m __;
   R_split_5 m l y d r0 _x _res r1 ll o rl ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_split_rect0 x f f0 f1 f2 l _res r1)
      ll o rl __;
   R_split_6 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_split_7 m l y d r0 _x _res r1 rl o rr ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_split_rect0 x f f0 f1 f2 r0 _res r1)
      rl o rr __}

r_split_rec0 :: S8 -> ((Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
                a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () ->
                (Triple2 a1) -> (R_split0 a1) -> a2 -> (Tree2 a1) -> (Option
                a1) -> (Tree2 a1) -> () -> a2) -> ((Tree2 a1) -> (Tree2 
                a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> () -> () -> a2)
                -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 
                a1) -> T -> () -> () -> () -> (Triple2 a1) -> (R_split0 
                a1) -> a2 -> (Tree2 a1) -> (Option a1) -> (Tree2 a1) -> () ->
                a2) -> (Tree2 a1) -> (Triple2 a1) -> (R_split0 a1) -> a2
r_split_rec0 =
  r_split_rect0

data R_map_option0 elt x =
   R_map_option_3 (Tree2 elt)
 | R_map_option_4 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T x (Tree2 x) 
 (R_map_option0 elt x) (Tree2 x) (R_map_option0 elt x)
 | R_map_option_5 (Tree2 elt) (Tree2 elt) Key2 elt (Tree2 elt) T (Tree2 x) 
 (R_map_option0 elt x) (Tree2 x) (R_map_option0 elt x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map_option_rect0 :: (Key2 -> a1 -> Option a2) -> ((Tree2 a1) -> () -> a3)
                      -> ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2
                      a1) -> T -> () -> a2 -> () -> (Tree2 a2) ->
                      (R_map_option0 a1 a2) -> a3 -> (Tree2 a2) ->
                      (R_map_option0 a1 a2) -> a3 -> a3) -> ((Tree2 a1) ->
                      (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> ()
                      -> (Tree2 a2) -> (R_map_option0 a1 a2) -> a3 -> (Tree2
                      a2) -> (R_map_option0 a1 a2) -> a3 -> a3) -> (Tree2 
                      a1) -> (Tree2 a2) -> (R_map_option0 a1 a2) -> a3
r_map_option_rect0 f f0 f1 f2 _ _ r =
  case r of {
   R_map_option_3 m -> f0 m __;
   R_map_option_4 m l x d r0 _x d' _res0 r1 _res r2 ->
    f1 m l x d r0 _x __ d' __ _res0 r1
      (r_map_option_rect0 f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect0 f f0 f1 f2 r0 _res r2);
   R_map_option_5 m l x d r0 _x _res0 r1 _res r2 ->
    f2 m l x d r0 _x __ __ _res0 r1
      (r_map_option_rect0 f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect0 f f0 f1 f2 r0 _res r2)}

r_map_option_rec0 :: (Key2 -> a1 -> Option a2) -> ((Tree2 a1) -> () -> a3) ->
                     ((Tree2 a1) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 
                     a1) -> T -> () -> a2 -> () -> (Tree2 a2) ->
                     (R_map_option0 a1 a2) -> a3 -> (Tree2 a2) ->
                     (R_map_option0 a1 a2) -> a3 -> a3) -> ((Tree2 a1) ->
                     (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> ()
                     -> (Tree2 a2) -> (R_map_option0 a1 a2) -> a3 -> (Tree2
                     a2) -> (R_map_option0 a1 a2) -> a3 -> a3) -> (Tree2 
                     a1) -> (Tree2 a2) -> (R_map_option0 a1 a2) -> a3
r_map_option_rec0 =
  r_map_option_rect0

data R_map2_opt0 elt x0 x =
   R_map2_opt_4 (Tree2 elt) (Tree2 x0)
 | R_map2_opt_5 (Tree2 elt) (Tree2 x0) (Tree2 elt) Key2 elt (Tree2 elt) 
 T
 | R_map2_opt_6 (Tree2 elt) (Tree2 x0) (Tree2 elt) Key2 elt (Tree2 elt) 
 T (Tree2 x0) Key2 x0 (Tree2 x0) T (Tree2 x0) (Option x0) (Tree2 x0) 
 x (Tree2 x) (R_map2_opt0 elt x0 x) (Tree2 x) (R_map2_opt0 elt x0 x)
 | R_map2_opt_7 (Tree2 elt) (Tree2 x0) (Tree2 elt) Key2 elt (Tree2 elt) 
 T (Tree2 x0) Key2 x0 (Tree2 x0) T (Tree2 x0) (Option x0) (Tree2 x0) 
 (Tree2 x) (R_map2_opt0 elt x0 x) (Tree2 x) (R_map2_opt0 elt x0 x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map2_opt_rect0 :: (Key2 -> a1 -> (Option a2) -> Option a3) -> ((Tree2 
                    a1) -> Tree2 a3) -> ((Tree2 a2) -> Tree2 a3) -> ((Tree2
                    a1) -> (Tree2 a2) -> () -> a4) -> ((Tree2 a1) -> (Tree2
                    a2) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> ()
                    -> () -> a4) -> ((Tree2 a1) -> (Tree2 a2) -> (Tree2 
                    a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                    a2) -> Key2 -> a2 -> (Tree2 a2) -> T -> () -> (Tree2 
                    a2) -> (Option a2) -> (Tree2 a2) -> () -> a3 -> () ->
                    (Tree2 a3) -> (R_map2_opt0 a1 a2 a3) -> a4 -> (Tree2 
                    a3) -> (R_map2_opt0 a1 a2 a3) -> a4 -> a4) -> ((Tree2 
                    a1) -> (Tree2 a2) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2
                    a1) -> T -> () -> (Tree2 a2) -> Key2 -> a2 -> (Tree2 
                    a2) -> T -> () -> (Tree2 a2) -> (Option a2) -> (Tree2 
                    a2) -> () -> () -> (Tree2 a3) -> (R_map2_opt0 a1 
                    a2 a3) -> a4 -> (Tree2 a3) -> (R_map2_opt0 a1 a2 
                    a3) -> a4 -> a4) -> (Tree2 a1) -> (Tree2 a2) -> (Tree2
                    a3) -> (R_map2_opt0 a1 a2 a3) -> a4
r_map2_opt_rect0 f mapl mapr f0 f1 f2 f3 _ _ _ r =
  case r of {
   R_map2_opt_4 m1 m2 -> f0 m1 m2 __;
   R_map2_opt_5 m1 m2 l1 x1 d1 r1 _x -> f1 m1 m2 l1 x1 d1 r1 _x __ __;
   R_map2_opt_6 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' e _res0
    r0 _res r2 ->
    f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
      _res0 r0 (r_map2_opt_rect0 f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
      _res r2 (r_map2_opt_rect0 f mapl mapr f0 f1 f2 f3 r1 r2' _res r2);
   R_map2_opt_7 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' _res0 r0
    _res r2 ->
    f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
      r0 (r_map2_opt_rect0 f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
      (r_map2_opt_rect0 f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)}

r_map2_opt_rec0 :: (Key2 -> a1 -> (Option a2) -> Option a3) -> ((Tree2 
                   a1) -> Tree2 a3) -> ((Tree2 a2) -> Tree2 a3) -> ((Tree2
                   a1) -> (Tree2 a2) -> () -> a4) -> ((Tree2 a1) -> (Tree2
                   a2) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> ()
                   -> () -> a4) -> ((Tree2 a1) -> (Tree2 a2) -> (Tree2 
                   a1) -> Key2 -> a1 -> (Tree2 a1) -> T -> () -> (Tree2 
                   a2) -> Key2 -> a2 -> (Tree2 a2) -> T -> () -> (Tree2 
                   a2) -> (Option a2) -> (Tree2 a2) -> () -> a3 -> () ->
                   (Tree2 a3) -> (R_map2_opt0 a1 a2 a3) -> a4 -> (Tree2 
                   a3) -> (R_map2_opt0 a1 a2 a3) -> a4 -> a4) -> ((Tree2 
                   a1) -> (Tree2 a2) -> (Tree2 a1) -> Key2 -> a1 -> (Tree2
                   a1) -> T -> () -> (Tree2 a2) -> Key2 -> a2 -> (Tree2 
                   a2) -> T -> () -> (Tree2 a2) -> (Option a2) -> (Tree2 
                   a2) -> () -> () -> (Tree2 a3) -> (R_map2_opt0 a1 a2 
                   a3) -> a4 -> (Tree2 a3) -> (R_map2_opt0 a1 a2 a3) -> a4 ->
                   a4) -> (Tree2 a1) -> (Tree2 a2) -> (Tree2 a3) ->
                   (R_map2_opt0 a1 a2 a3) -> a4
r_map2_opt_rec0 =
  r_map2_opt_rect0

fold'0 :: (Key2 -> a1 -> a2 -> a2) -> (Tree2 a1) -> a2 -> a2
fold'0 f s =
  fold9 f (elements8 s)

flatten_e2 :: (Enumeration2 a1) -> List (Prod Key2 a1)
flatten_e2 e =
  case e of {
   End2 -> Nil;
   More2 x e0 t r -> Cons (Pair x e0) (app (elements8 t) (flatten_e2 r))}

type Bst0 elt = Tree2 elt
  -- singleton inductive, whose constructor was Bst
  
this2 :: (Bst0 a1) -> Tree2 a1
this2 b =
  b

type T37 elt = Bst0 elt

type Key4 = S8

empty10 :: T37 a1
empty10 =
  empty8

is_empty10 :: (T37 a1) -> Bool
is_empty10 m =
  is_empty8 (this2 m)

add13 :: Key4 -> a1 -> (T37 a1) -> T37 a1
add13 x e m =
  add11 x e (this2 m)

remove10 :: Key4 -> (T37 a1) -> T37 a1
remove10 x m =
  remove8 x (this2 m)

mem10 :: Key4 -> (T37 a1) -> Bool
mem10 x m =
  mem8 x (this2 m)

find4 :: Key4 -> (T37 a1) -> Option a1
find4 x m =
  find2 x (this2 m)

map10 :: (a1 -> a2) -> (T37 a1) -> T37 a2
map10 f m =
  map6 f (this2 m)

mapi4 :: (Key4 -> a1 -> a2) -> (T37 a1) -> T37 a2
mapi4 f m =
  mapi2 f (this2 m)

map11 :: ((Option a1) -> (Option a2) -> Option a3) -> (T37 a1) -> (T37 
         a2) -> T37 a3
map11 f m m' =
  map7 f (this2 m) (this2 m')

elements10 :: (T37 a1) -> List (Prod Key4 a1)
elements10 m =
  elements8 (this2 m)

cardinal8 :: (T37 a1) -> Nat
cardinal8 m =
  cardinal7 (this2 m)

fold10 :: (Key4 -> a1 -> a2 -> a2) -> (T37 a1) -> a2 -> a2
fold10 f m i =
  fold8 f (this2 m) i

equal10 :: (a1 -> a1 -> Bool) -> (T37 a1) -> (T37 a1) -> Bool
equal10 cmp m m' =
  equal8 cmp (this2 m) (this2 m')

emptyICMap :: T37 ConcreteChoice
emptyICMap =
  empty10

data InputT =
   Input T9 T20 (T29 Cash) (T37 ConcreteChoice)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

cc :: InputT -> T9
cc i =
  case i of {
   Input cc0 _ _ _ -> cc0}

rc :: InputT -> T20
rc i =
  case i of {
   Input _ rc0 _ _ -> rc0}

rp :: InputT -> T29 Cash
rp i =
  case i of {
   Input _ _ rp0 _ -> rp0}

emptyInput :: InputT
emptyInput =
  Input emptyCCSet emptyRCSet emptyRPMap emptyICMap

data Action =
   SuccessfulPay IdentPayT Person Person Cash
 | ExpiredPay IdentPayT Person Person Cash
 | FailedPay IdentPayT Person Person Cash
 | SuccessfulCommit IdentCCT Person Cash Timeout
 | CommitRedeemed IdentCCT Person Cash
 | ExpiredCommitRedeemed IdentCCT Person Cash
 | DuplicateRedeem IdentCCT Person
 | ChoiceMade IdentChoiceT Person ConcreteChoice
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

type AS = List Action

data CCRedeemStatus =
   NotRedeemed Cash Timeout
 | ExpiredAndRedeemed
 | ManuallyRedeemed
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

type CCStatus = Prod Person CCRedeemStatus

type S10 = IdentCCT

type S11 = S10

st5 :: S11 -> List Prelude.Integer
st5 x =
  Cons x Nil

type T38 = S11

compareList5 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList5 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec5 :: T38 -> T38 -> Sumor Sumbool
compareDec5 x y =
  compareList5 (Cons x Nil) (Cons y Nil)

compare27 :: T38 -> T38 -> Compare T38
compare27 x y =
  let {h = compareDec5 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec37 :: T38 -> T38 -> Sumbool
eq_dec37 x y =
  let {h = compareDec5 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type S12 = S10

st6 :: S12 -> List Prelude.Integer
st6 x =
  Cons x Nil

type T39 = S12

compareList6 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList6 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec6 :: T39 -> T39 -> Sumor Sumbool
compareDec6 x y =
  compareList6 (Cons x Nil) (Cons y Nil)

compare28 :: T39 -> T39 -> Compare T39
compare28 x y =
  let {h = compareDec6 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec38 :: T39 -> T39 -> Sumbool
eq_dec38 x y =
  let {h = compareDec6 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type Key5 = S11

data Tree3 elt =
   Leaf3
 | Node3 (Tree3 elt) Key5 elt (Tree3 elt) T
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

tree_rect1 :: a2 -> ((Tree3 a1) -> a2 -> Key5 -> a1 -> (Tree3 a1) -> a2 -> T
              -> a2) -> (Tree3 a1) -> a2
tree_rect1 f f0 t =
  case t of {
   Leaf3 -> f;
   Node3 t0 k e t1 t2 ->
    f0 t0 (tree_rect1 f f0 t0) k e t1 (tree_rect1 f f0 t1) t2}

tree_rec1 :: a2 -> ((Tree3 a1) -> a2 -> Key5 -> a1 -> (Tree3 a1) -> a2 -> T
             -> a2) -> (Tree3 a1) -> a2
tree_rec1 =
  tree_rect1

height3 :: (Tree3 a1) -> T
height3 m =
  case m of {
   Leaf3 -> _0;
   Node3 _ _ _ _ h -> h}

cardinal9 :: (Tree3 a1) -> Nat
cardinal9 m =
  case m of {
   Leaf3 -> O;
   Node3 l _ _ r _ -> S (add (cardinal9 l) (cardinal9 r))}

empty11 :: Tree3 a1
empty11 =
  Leaf3

is_empty11 :: (Tree3 a1) -> Bool
is_empty11 m =
  case m of {
   Leaf3 -> True;
   Node3 _ _ _ _ _ -> False}

mem11 :: S11 -> (Tree3 a1) -> Bool
mem11 x m =
  case m of {
   Leaf3 -> False;
   Node3 l y _ r _ ->
    case compare27 x y of {
     LT -> mem11 x l;
     EQ -> True;
     GT -> mem11 x r}}

find5 :: S11 -> (Tree3 a1) -> Option a1
find5 x m =
  case m of {
   Leaf3 -> None;
   Node3 l y d r _ ->
    case compare27 x y of {
     LT -> find5 x l;
     EQ -> Some d;
     GT -> find5 x r}}

create3 :: (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> Tree3 a1
create3 l x e r =
  Node3 l x e r (add1 (max0 (height3 l) (height3 r)) _1)

assert_false3 :: (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> Tree3 a1
assert_false3 =
  create3

bal3 :: (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> Tree3 a1
bal3 l x d r =
  let {hl = height3 l} in
  let {hr = height3 r} in
  case gt_le_dec hl (add1 hr _2) of {
   Left ->
    case l of {
     Leaf3 -> assert_false3 l x d r;
     Node3 ll lx ld lr _ ->
      case ge_lt_dec (height3 ll) (height3 lr) of {
       Left -> create3 ll lx ld (create3 lr x d r);
       Right ->
        case lr of {
         Leaf3 -> assert_false3 l x d r;
         Node3 lrl lrx lrd lrr _ ->
          create3 (create3 ll lx ld lrl) lrx lrd (create3 lrr x d r)}}};
   Right ->
    case gt_le_dec hr (add1 hl _2) of {
     Left ->
      case r of {
       Leaf3 -> assert_false3 l x d r;
       Node3 rl rx rd rr _ ->
        case ge_lt_dec (height3 rr) (height3 rl) of {
         Left -> create3 (create3 l x d rl) rx rd rr;
         Right ->
          case rl of {
           Leaf3 -> assert_false3 l x d r;
           Node3 rll rlx rld rlr _ ->
            create3 (create3 l x d rll) rlx rld (create3 rlr rx rd rr)}}};
     Right -> create3 l x d r}}

add14 :: Key5 -> a1 -> (Tree3 a1) -> Tree3 a1
add14 x d m =
  case m of {
   Leaf3 -> Node3 Leaf3 x d Leaf3 _1;
   Node3 l y d' r h ->
    case compare27 x y of {
     LT -> bal3 (add14 x d l) y d' r;
     EQ -> Node3 l y d r h;
     GT -> bal3 l y d' (add14 x d r)}}

remove_min3 :: (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> Prod (Tree3 a1)
               (Prod Key5 a1)
remove_min3 l x d r =
  case l of {
   Leaf3 -> Pair r (Pair x d);
   Node3 ll lx ld lr _ ->
    case remove_min3 ll lx ld lr of {
     Pair l' m -> Pair (bal3 l' x d r) m}}

merge3 :: (Tree3 a1) -> (Tree3 a1) -> Tree3 a1
merge3 s1 s2 =
  case s1 of {
   Leaf3 -> s2;
   Node3 _ _ _ _ _ ->
    case s2 of {
     Leaf3 -> s1;
     Node3 l2 x2 d2 r2 _ ->
      case remove_min3 l2 x2 d2 r2 of {
       Pair s2' p -> case p of {
                      Pair x d -> bal3 s1 x d s2'}}}}

remove11 :: S11 -> (Tree3 a1) -> Tree3 a1
remove11 x m =
  case m of {
   Leaf3 -> Leaf3;
   Node3 l y d r _ ->
    case compare27 x y of {
     LT -> bal3 (remove11 x l) y d r;
     EQ -> merge3 l r;
     GT -> bal3 l y d (remove11 x r)}}

join3 :: (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> Tree3 a1
join3 l =
  case l of {
   Leaf3 -> add14;
   Node3 ll lx ld lr lh -> (\x d ->
    let {
     join_aux r =
       case r of {
        Leaf3 -> add14 x d l;
        Node3 rl rx rd rr rh ->
         case gt_le_dec lh (add1 rh _2) of {
          Left -> bal3 ll lx ld (join3 lr x d r);
          Right ->
           case gt_le_dec rh (add1 lh _2) of {
            Left -> bal3 (join_aux rl) rx rd rr;
            Right -> create3 l x d r}}}}
    in join_aux)}

data Triple3 elt =
   Mktriple3 (Tree3 elt) (Option elt) (Tree3 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

t_left3 :: (Triple3 a1) -> Tree3 a1
t_left3 t =
  case t of {
   Mktriple3 t_left5 _ _ -> t_left5}

t_opt1 :: (Triple3 a1) -> Option a1
t_opt1 t =
  case t of {
   Mktriple3 _ t_opt3 _ -> t_opt3}

t_right3 :: (Triple3 a1) -> Tree3 a1
t_right3 t =
  case t of {
   Mktriple3 _ _ t_right5 -> t_right5}

split3 :: S11 -> (Tree3 a1) -> Triple3 a1
split3 x m =
  case m of {
   Leaf3 -> Mktriple3 Leaf3 None Leaf3;
   Node3 l y d r _ ->
    case compare27 x y of {
     LT ->
      case split3 x l of {
       Mktriple3 ll o rl -> Mktriple3 ll o (join3 rl y d r)};
     EQ -> Mktriple3 l (Some d) r;
     GT ->
      case split3 x r of {
       Mktriple3 rl o rr -> Mktriple3 (join3 l y d rl) o rr}}}

concat3 :: (Tree3 a1) -> (Tree3 a1) -> Tree3 a1
concat3 m1 m2 =
  case m1 of {
   Leaf3 -> m2;
   Node3 _ _ _ _ _ ->
    case m2 of {
     Leaf3 -> m1;
     Node3 l2 x2 d2 r2 _ ->
      case remove_min3 l2 x2 d2 r2 of {
       Pair m2' xd -> join3 m1 (fst xd) (snd xd) m2'}}}

elements_aux3 :: (List (Prod Key5 a1)) -> (Tree3 a1) -> List (Prod Key5 a1)
elements_aux3 acc m =
  case m of {
   Leaf3 -> acc;
   Node3 l x d r _ -> elements_aux3 (Cons (Pair x d) (elements_aux3 acc r)) l}

elements11 :: (Tree3 a1) -> List (Prod Key5 a1)
elements11 =
  elements_aux3 Nil

fold11 :: (Key5 -> a1 -> a2 -> a2) -> (Tree3 a1) -> a2 -> a2
fold11 f m a =
  case m of {
   Leaf3 -> a;
   Node3 l x d r _ -> fold11 f r (f x d (fold11 f l a))}

data Enumeration3 elt =
   End3
 | More3 Key5 elt (Tree3 elt) (Enumeration3 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

enumeration_rect1 :: a2 -> (Key5 -> a1 -> (Tree3 a1) -> (Enumeration3 
                     a1) -> a2 -> a2) -> (Enumeration3 a1) -> a2
enumeration_rect1 f f0 e =
  case e of {
   End3 -> f;
   More3 k e0 t e1 -> f0 k e0 t e1 (enumeration_rect1 f f0 e1)}

enumeration_rec1 :: a2 -> (Key5 -> a1 -> (Tree3 a1) -> (Enumeration3 
                    a1) -> a2 -> a2) -> (Enumeration3 a1) -> a2
enumeration_rec1 =
  enumeration_rect1

cons3 :: (Tree3 a1) -> (Enumeration3 a1) -> Enumeration3 a1
cons3 m e =
  case m of {
   Leaf3 -> e;
   Node3 l x d r _ -> cons3 l (More3 x d r e)}

equal_more1 :: (a1 -> a1 -> Bool) -> S11 -> a1 -> ((Enumeration3 a1) -> Bool)
               -> (Enumeration3 a1) -> Bool
equal_more1 cmp x1 d1 cont e2 =
  case e2 of {
   End3 -> False;
   More3 x2 d2 r2 e3 ->
    case compare27 x1 x2 of {
     EQ -> case cmp d1 d2 of {
            True -> cont (cons3 r2 e3);
            False -> False};
     _ -> False}}

equal_cont1 :: (a1 -> a1 -> Bool) -> (Tree3 a1) -> ((Enumeration3 a1) ->
               Bool) -> (Enumeration3 a1) -> Bool
equal_cont1 cmp m1 cont e2 =
  case m1 of {
   Leaf3 -> cont e2;
   Node3 l1 x1 d1 r1 _ ->
    equal_cont1 cmp l1 (equal_more1 cmp x1 d1 (equal_cont1 cmp r1 cont)) e2}

equal_end1 :: (Enumeration3 a1) -> Bool
equal_end1 e2 =
  case e2 of {
   End3 -> True;
   More3 _ _ _ _ -> False}

equal11 :: (a1 -> a1 -> Bool) -> (Tree3 a1) -> (Tree3 a1) -> Bool
equal11 cmp m1 m2 =
  equal_cont1 cmp m1 equal_end1 (cons3 m2 End3)

map12 :: (a1 -> a2) -> (Tree3 a1) -> Tree3 a2
map12 f m =
  case m of {
   Leaf3 -> Leaf3;
   Node3 l x d r h -> Node3 (map12 f l) x (f d) (map12 f r) h}

mapi5 :: (Key5 -> a1 -> a2) -> (Tree3 a1) -> Tree3 a2
mapi5 f m =
  case m of {
   Leaf3 -> Leaf3;
   Node3 l x d r h -> Node3 (mapi5 f l) x (f x d) (mapi5 f r) h}

map_option1 :: (Key5 -> a1 -> Option a2) -> (Tree3 a1) -> Tree3 a2
map_option1 f m =
  case m of {
   Leaf3 -> Leaf3;
   Node3 l x d r _ ->
    case f x d of {
     Some d' -> join3 (map_option1 f l) x d' (map_option1 f r);
     None -> concat3 (map_option1 f l) (map_option1 f r)}}

map2_opt1 :: (Key5 -> a1 -> (Option a2) -> Option a3) -> ((Tree3 a1) -> Tree3
             a3) -> ((Tree3 a2) -> Tree3 a3) -> (Tree3 a1) -> (Tree3 
             a2) -> Tree3 a3
map2_opt1 f mapl mapr m1 m2 =
  case m1 of {
   Leaf3 -> mapr m2;
   Node3 l1 x1 d1 r1 _ ->
    case m2 of {
     Leaf3 -> mapl m1;
     Node3 _ _ _ _ _ ->
      case split3 x1 m2 of {
       Mktriple3 l2' o2 r2' ->
        case f x1 d1 o2 of {
         Some e ->
          join3 (map2_opt1 f mapl mapr l1 l2') x1 e
            (map2_opt1 f mapl mapr r1 r2');
         None ->
          concat3 (map2_opt1 f mapl mapr l1 l2')
            (map2_opt1 f mapl mapr r1 r2')}}}}

map13 :: ((Option a1) -> (Option a2) -> Option a3) -> (Tree3 a1) -> (Tree3
         a2) -> Tree3 a3
map13 f =
  map2_opt1 (\_ d o -> f (Some d) o) (map_option1 (\_ d -> f (Some d) None))
    (map_option1 (\_ d' -> f None (Some d')))

type T40 = S11

eq_dec39 :: S11 -> S11 -> Sumbool
eq_dec39 =
  eq_dec37

lt_dec11 :: S11 -> S11 -> Sumbool
lt_dec11 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare27 x y)

eqb15 :: S11 -> S11 -> Bool
eqb15 x y =
  case eq_dec39 x y of {
   Left -> True;
   Right -> False}

type T41 = S11

eq_dec40 :: S11 -> S11 -> Sumbool
eq_dec40 =
  eq_dec37

lt_dec12 :: S11 -> S11 -> Sumbool
lt_dec12 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare27 x y)

eqb16 :: S11 -> S11 -> Bool
eqb16 x y =
  case eq_dec40 x y of {
   Left -> True;
   Right -> False}

type T42 = S11

eq_dec41 :: S11 -> S11 -> Sumbool
eq_dec41 =
  eq_dec37

lt_dec13 :: S11 -> S11 -> Sumbool
lt_dec13 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare27 x y)

eqb17 :: S11 -> S11 -> Bool
eqb17 x y =
  case eq_dec41 x y of {
   Left -> True;
   Right -> False}

type T43 = S11

eq_dec42 :: S11 -> S11 -> Sumbool
eq_dec42 =
  eq_dec37

lt_dec14 :: S11 -> S11 -> Sumbool
lt_dec14 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare27 x y)

eqb18 :: S11 -> S11 -> Bool
eqb18 x y =
  case eq_dec42 x y of {
   Left -> True;
   Right -> False}

type Key6 = S11

type T44 elt = List (Prod S11 elt)

empty12 :: T44 a1
empty12 =
  Nil

is_empty12 :: (T44 a1) -> Bool
is_empty12 l =
  case l of {
   Nil -> True;
   Cons _ _ -> False}

mem12 :: Key6 -> (T44 a1) -> Bool
mem12 k s =
  case s of {
   Nil -> False;
   Cons p l ->
    case p of {
     Pair k' _ ->
      case compare27 k k' of {
       LT -> False;
       EQ -> True;
       GT -> mem12 k l}}}

data R_mem3 elt =
   R_mem_16 (T44 elt)
 | R_mem_17 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_mem_18 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_mem_19 (T44 elt) S11 elt (List (Prod S11 elt)) Bool (R_mem3 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect3 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
               (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
               a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
               a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
               () -> () -> Bool -> (R_mem3 a1) -> a2 -> a2) -> (T44 a1) ->
               Bool -> (R_mem3 a1) -> a2
r_mem_rect3 k f f0 f1 f2 _ _ r =
  case r of {
   R_mem_16 s -> f s __;
   R_mem_17 s k' _x l -> f0 s k' _x l __ __ __;
   R_mem_18 s k' _x l -> f1 s k' _x l __ __ __;
   R_mem_19 s k' _x l _res r0 ->
    f2 s k' _x l __ __ __ _res r0 (r_mem_rect3 k f f0 f1 f2 l _res r0)}

r_mem_rec3 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
              (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
              a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
              a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
              () -> () -> Bool -> (R_mem3 a1) -> a2 -> a2) -> (T44 a1) ->
              Bool -> (R_mem3 a1) -> a2
r_mem_rec3 =
  r_mem_rect3

mem_rect1 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
             (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 a1) ->
             S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () -> a2) ->
             ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> ()
             -> a2 -> a2) -> (T44 a1) -> a2
mem_rect1 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> False;
      Cons p l ->
       case p of {
        Pair k' _ ->
         case compare27 k k' of {
          LT -> False;
          EQ -> True;
          GT -> mem12 k l}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = mem_rect1 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare27 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (mem12 k s)

mem_rec1 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 -> (List
            (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 a1) -> S11 -> a1
            -> (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
            a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () -> a2
            -> a2) -> (T44 a1) -> a2
mem_rec1 =
  mem_rect1

r_mem_correct1 :: Key6 -> (T44 a1) -> Bool -> R_mem3 a1
r_mem_correct1 k s _res =
  unsafeCoerce mem_rect1 k (\y _ z _ -> eq_rect_r False (R_mem_16 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r False (R_mem_17 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r True (R_mem_18 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (mem12 k y2) (R_mem_19 y y0 y1 y2 (mem12 k y2)
      (y6 (mem12 k y2) __)) z) s _res __

find6 :: Key6 -> (T44 a1) -> Option a1
find6 k s =
  case s of {
   Nil -> None;
   Cons p s' ->
    case p of {
     Pair k' x ->
      case compare27 k k' of {
       LT -> None;
       EQ -> Some x;
       GT -> find6 k s'}}}

data R_find3 elt =
   R_find_16 (T44 elt)
 | R_find_17 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_find_18 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_find_19 (T44 elt) S11 elt (List (Prod S11 elt)) (Option elt) (R_find3
                                                                  elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect3 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
                (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
                a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
                a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> ()
                -> () -> () -> (Option a1) -> (R_find3 a1) -> a2 -> a2) ->
                (T44 a1) -> (Option a1) -> (R_find3 a1) -> a2
r_find_rect3 k f f0 f1 f2 _ _ r =
  case r of {
   R_find_16 s -> f s __;
   R_find_17 s k' x s' -> f0 s k' x s' __ __ __;
   R_find_18 s k' x s' -> f1 s k' x s' __ __ __;
   R_find_19 s k' x s' _res r0 ->
    f2 s k' x s' __ __ __ _res r0 (r_find_rect3 k f f0 f1 f2 s' _res r0)}

r_find_rec3 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
               (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
               a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
               a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
               () -> () -> (Option a1) -> (R_find3 a1) -> a2 -> a2) -> (T44
               a1) -> (Option a1) -> (R_find3 a1) -> a2
r_find_rec3 =
  r_find_rect3

find_rect1 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
              (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
              a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
              a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
              () -> () -> a2 -> a2) -> (T44 a1) -> a2
find_rect1 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> None;
      Cons p s' ->
       case p of {
        Pair k' x ->
         case compare27 k k' of {
          LT -> None;
          EQ -> Some x;
          GT -> find6 k s'}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = find_rect1 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare27 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (find6 k s)

find_rec1 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
             (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 a1) ->
             S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () -> a2) ->
             ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> ()
             -> a2 -> a2) -> (T44 a1) -> a2
find_rec1 =
  find_rect1

r_find_correct1 :: Key6 -> (T44 a1) -> (Option a1) -> R_find3 a1
r_find_correct1 k s _res =
  unsafeCoerce find_rect1 k (\y _ z _ -> eq_rect_r None (R_find_16 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r None (R_find_17 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r (Some y1) (R_find_18 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (find6 k y2) (R_find_19 y y0 y1 y2 (find6 k y2)
      (y6 (find6 k y2) __)) z) s _res __

add15 :: Key6 -> a1 -> (T44 a1) -> T44 a1
add15 k x s =
  case s of {
   Nil -> Cons (Pair k x) Nil;
   Cons p l ->
    case p of {
     Pair k' y ->
      case compare27 k k' of {
       LT -> Cons (Pair k x) s;
       EQ -> Cons (Pair k x) l;
       GT -> Cons (Pair k' y) (add15 k x l)}}}

data R_add3 elt =
   R_add_16 (T44 elt)
 | R_add_17 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_add_18 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_add_19 (T44 elt) S11 elt (List (Prod S11 elt)) (T44 elt) (R_add3 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect3 :: Key6 -> a1 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1
               -> (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
               a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
               a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
               () -> () -> (T44 a1) -> (R_add3 a1) -> a2 -> a2) -> (T44 
               a1) -> (T44 a1) -> (R_add3 a1) -> a2
r_add_rect3 k x f f0 f1 f2 _ _ r =
  case r of {
   R_add_16 s -> f s __;
   R_add_17 s k' y l -> f0 s k' y l __ __ __;
   R_add_18 s k' y l -> f1 s k' y l __ __ __;
   R_add_19 s k' y l _res r0 ->
    f2 s k' y l __ __ __ _res r0 (r_add_rect3 k x f f0 f1 f2 l _res r0)}

r_add_rec3 :: Key6 -> a1 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1
              -> (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
              a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
              a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
              () -> () -> (T44 a1) -> (R_add3 a1) -> a2 -> a2) -> (T44 
              a1) -> (T44 a1) -> (R_add3 a1) -> a2
r_add_rec3 =
  r_add_rect3

add_rect1 :: Key6 -> a1 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1
             -> (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
             a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
             a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
             () -> () -> a2 -> a2) -> (T44 a1) -> a2
add_rect1 k x f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Cons (Pair k x) Nil;
      Cons p l ->
       case p of {
        Pair k' y ->
         case compare27 k k' of {
          LT -> Cons (Pair k x) s;
          EQ -> Cons (Pair k x) l;
          GT -> Cons (Pair k' y) (add15 k x l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = add_rect1 k x f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare27 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (add15 k x s)

add_rec1 :: Key6 -> a1 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
            (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 a1) -> S11
            -> a1 -> (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44
            a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () -> a2
            -> a2) -> (T44 a1) -> a2
add_rec1 =
  add_rect1

r_add_correct1 :: Key6 -> a1 -> (T44 a1) -> (T44 a1) -> R_add3 a1
r_add_correct1 k x s _res =
  add_rect1 k x (\y _ z _ -> eq_rect_r (Cons (Pair k x) Nil) (R_add_16 y) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y) (R_add_17 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y2) (R_add_18 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (add15 k x y2)) (R_add_19 y y0 y1 y2
      (add15 k x y2) (y6 (add15 k x y2) __)) z) s _res __

remove12 :: Key6 -> (T44 a1) -> T44 a1
remove12 k s =
  case s of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k' x ->
      case compare27 k k' of {
       LT -> s;
       EQ -> l;
       GT -> Cons (Pair k' x) (remove12 k l)}}}

data R_remove3 elt =
   R_remove_16 (T44 elt)
 | R_remove_17 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_remove_18 (T44 elt) S11 elt (List (Prod S11 elt))
 | R_remove_19 (T44 elt) S11 elt (List (Prod S11 elt)) (T44 elt) (R_remove3
                                                                 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect3 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
                  (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
                  a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> ()
                  -> a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) ->
                  () -> () -> () -> (T44 a1) -> (R_remove3 a1) -> a2 -> a2)
                  -> (T44 a1) -> (T44 a1) -> (R_remove3 a1) -> a2
r_remove_rect3 k f f0 f1 f2 _ _ r =
  case r of {
   R_remove_16 s -> f s __;
   R_remove_17 s k' x l -> f0 s k' x l __ __ __;
   R_remove_18 s k' x l -> f1 s k' x l __ __ __;
   R_remove_19 s k' x l _res r0 ->
    f2 s k' x l __ __ __ _res r0 (r_remove_rect3 k f f0 f1 f2 l _res r0)}

r_remove_rec3 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
                 (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
                 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> ()
                 -> a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) ->
                 () -> () -> () -> (T44 a1) -> (R_remove3 a1) -> a2 -> a2) ->
                 (T44 a1) -> (T44 a1) -> (R_remove3 a1) -> a2
r_remove_rec3 =
  r_remove_rect3

remove_rect1 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
                (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
                a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
                a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> ()
                -> () -> () -> a2 -> a2) -> (T44 a1) -> a2
remove_rect1 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Nil;
      Cons p l ->
       case p of {
        Pair k' x ->
         case compare27 k k' of {
          LT -> s;
          EQ -> l;
          GT -> Cons (Pair k' x) (remove12 k l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = remove_rect1 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare27 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (remove12 k s)

remove_rec1 :: Key6 -> ((T44 a1) -> () -> a2) -> ((T44 a1) -> S11 -> a1 ->
               (List (Prod S11 a1)) -> () -> () -> () -> a2) -> ((T44 
               a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
               a2) -> ((T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
               () -> () -> a2 -> a2) -> (T44 a1) -> a2
remove_rec1 =
  remove_rect1

r_remove_correct1 :: Key6 -> (T44 a1) -> (T44 a1) -> R_remove3 a1
r_remove_correct1 k s _res =
  unsafeCoerce remove_rect1 k (\y _ z _ -> eq_rect_r Nil (R_remove_16 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y (R_remove_17 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y2 (R_remove_18 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (remove12 k y2)) (R_remove_19 y y0 y1 y2
      (remove12 k y2) (y6 (remove12 k y2) __)) z) s _res __

elements12 :: (T44 a1) -> T44 a1
elements12 m =
  m

fold12 :: (Key6 -> a1 -> a2 -> a2) -> (T44 a1) -> a2 -> a2
fold12 f m acc =
  case m of {
   Nil -> acc;
   Cons p m' -> case p of {
                 Pair k e -> fold12 f m' (f k e acc)}}

data R_fold1 elt a =
   R_fold_4 (T44 elt) a
 | R_fold_5 (T44 elt) a S11 elt (List (Prod S11 elt)) a (R_fold1 elt a)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_fold_rect1 :: (Key6 -> a1 -> a2 -> a2) -> ((T44 a1) -> a2 -> () -> a3) ->
                ((T44 a1) -> a2 -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
                a2 -> (R_fold1 a1 a2) -> a3 -> a3) -> (T44 a1) -> a2 -> a2 ->
                (R_fold1 a1 a2) -> a3
r_fold_rect1 f f0 f1 _ _ _ r =
  case r of {
   R_fold_4 m acc -> f0 m acc __;
   R_fold_5 m acc k e m' _res r0 ->
    f1 m acc k e m' __ _res r0 (r_fold_rect1 f f0 f1 m' (f k e acc) _res r0)}

r_fold_rec1 :: (Key6 -> a1 -> a2 -> a2) -> ((T44 a1) -> a2 -> () -> a3) ->
               ((T44 a1) -> a2 -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
               a2 -> (R_fold1 a1 a2) -> a3 -> a3) -> (T44 a1) -> a2 -> a2 ->
               (R_fold1 a1 a2) -> a3
r_fold_rec1 =
  r_fold_rect1

fold_rect1 :: (Key6 -> a1 -> a2 -> a2) -> ((T44 a1) -> a2 -> () -> a3) ->
              ((T44 a1) -> a2 -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
              a3 -> a3) -> (T44 a1) -> a2 -> a3
fold_rect1 f1 f0 f m acc =
  eq_rect_r
    (case m of {
      Nil -> acc;
      Cons p m' -> case p of {
                    Pair k e -> fold12 f1 m' (f1 k e acc)}})
    (let {f2 = f0 m acc} in
     let {f3 = f m acc} in
     case m of {
      Nil -> f2 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f4 = f3 t0 e l __} in
         let {hrec = fold_rect1 f1 f0 f l (f1 t0 e acc)} in f4 hrec}})
    (fold12 f1 m acc)

fold_rec1 :: (Key6 -> a1 -> a2 -> a2) -> ((T44 a1) -> a2 -> () -> a3) ->
             ((T44 a1) -> a2 -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> a3
             -> a3) -> (T44 a1) -> a2 -> a3
fold_rec1 =
  fold_rect1

r_fold_correct1 :: (Key6 -> a1 -> a2 -> a2) -> (T44 a1) -> a2 -> a2 ->
                   R_fold1 a1 a2
r_fold_correct1 f m acc _res =
  fold_rect1 f (\y y0 _ z _ -> eq_rect_r y0 (R_fold_4 y y0) z)
    (\y y0 y1 y2 y3 _ y5 z _ ->
    eq_rect_r (fold12 f y3 (f y1 y2 y0)) (R_fold_5 y y0 y1 y2 y3
      (fold12 f y3 (f y1 y2 y0)) (y5 (fold12 f y3 (f y1 y2 y0)) __)) z) m acc
    _res __

equal12 :: (a1 -> a1 -> Bool) -> (T44 a1) -> (T44 a1) -> Bool
equal12 cmp m m' =
  case m of {
   Nil -> case m' of {
           Nil -> True;
           Cons _ _ -> False};
   Cons p l ->
    case p of {
     Pair x e ->
      case m' of {
       Nil -> False;
       Cons p0 l' ->
        case p0 of {
         Pair x' e' ->
          case compare27 x x' of {
           EQ -> andb (cmp e e') (equal12 cmp l l');
           _ -> False}}}}}

data R_equal1 elt =
   R_equal_8 (T44 elt) (T44 elt)
 | R_equal_9 (T44 elt) (T44 elt) S11 elt (List (Prod S11 elt)) S11 elt 
 (List (Prod S11 elt)) Bool (R_equal1 elt)
 | R_equal_10 (T44 elt) (T44 elt) S11 elt (List (Prod S11 elt)) S11 elt 
 (List (Prod S11 elt)) (Compare S11)
 | R_equal_11 (T44 elt) (T44 elt) (T44 elt) (T44 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_equal_rect1 :: (a1 -> a1 -> Bool) -> ((T44 a1) -> (T44 a1) -> () -> () ->
                 a2) -> ((T44 a1) -> (T44 a1) -> S11 -> a1 -> (List
                 (Prod S11 a1)) -> () -> S11 -> a1 -> (List (Prod S11 a1)) ->
                 () -> () -> () -> Bool -> (R_equal1 a1) -> a2 -> a2) ->
                 ((T44 a1) -> (T44 a1) -> S11 -> a1 -> (List (Prod S11 a1))
                 -> () -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> (Compare
                 S11) -> () -> () -> a2) -> ((T44 a1) -> (T44 a1) -> (T44 
                 a1) -> () -> (T44 a1) -> () -> () -> a2) -> (T44 a1) -> (T44
                 a1) -> Bool -> (R_equal1 a1) -> a2
r_equal_rect1 cmp f f0 f1 f2 _ _ _ r =
  case r of {
   R_equal_8 m m' -> f m m' __ __;
   R_equal_9 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (r_equal_rect1 cmp f f0 f1 f2 l l' _res r0);
   R_equal_10 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   R_equal_11 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

r_equal_rec1 :: (a1 -> a1 -> Bool) -> ((T44 a1) -> (T44 a1) -> () -> () ->
                a2) -> ((T44 a1) -> (T44 a1) -> S11 -> a1 -> (List
                (Prod S11 a1)) -> () -> S11 -> a1 -> (List (Prod S11 a1)) ->
                () -> () -> () -> Bool -> (R_equal1 a1) -> a2 -> a2) -> ((T44
                a1) -> (T44 a1) -> S11 -> a1 -> (List (Prod S11 a1)) -> () ->
                S11 -> a1 -> (List (Prod S11 a1)) -> () -> (Compare S11) ->
                () -> () -> a2) -> ((T44 a1) -> (T44 a1) -> (T44 a1) -> () ->
                (T44 a1) -> () -> () -> a2) -> (T44 a1) -> (T44 a1) -> Bool
                -> (R_equal1 a1) -> a2
r_equal_rec1 =
  r_equal_rect1

equal_rect1 :: (a1 -> a1 -> Bool) -> ((T44 a1) -> (T44 a1) -> () -> () -> a2)
               -> ((T44 a1) -> (T44 a1) -> S11 -> a1 -> (List (Prod S11 a1))
               -> () -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> ()
               -> a2 -> a2) -> ((T44 a1) -> (T44 a1) -> S11 -> a1 -> (List
               (Prod S11 a1)) -> () -> S11 -> a1 -> (List (Prod S11 a1)) ->
               () -> (Compare S11) -> () -> () -> a2) -> ((T44 a1) -> (T44
               a1) -> (T44 a1) -> () -> (T44 a1) -> () -> () -> a2) -> (T44
               a1) -> (T44 a1) -> a2
equal_rect1 cmp f2 f1 f0 f m m' =
  eq_rect_r
    (case m of {
      Nil -> case m' of {
              Nil -> True;
              Cons _ _ -> False};
      Cons p l ->
       case p of {
        Pair x e ->
         case m' of {
          Nil -> False;
          Cons p0 l' ->
           case p0 of {
            Pair x' e' ->
             case compare27 x x' of {
              EQ -> andb (cmp e e') (equal12 cmp l l');
              _ -> False}}}}})
    (let {f3 = f2 m m'} in
     let {f4 = f1 m m'} in
     let {f5 = f0 m m'} in
     let {f6 = f m m'} in
     let {f7 = f6 m __} in
     let {f8 = f7 m' __} in
     case m of {
      Nil ->
       let {f9 = f3 __} in case m' of {
                            Nil -> f9 __;
                            Cons _ _ -> f8 __};
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case m' of {
          Nil -> f8 __;
          Cons p0 l0 ->
           case p0 of {
            Pair t1 e0 ->
             let {f11 = f9 t1 e0 l0 __} in
             let {f12 = let {_x = compare27 t0 t1} in f11 _x __} in
             let {f13 = f10 t1 e0 l0 __} in
             let {
              f14 = \_ _ ->
               let {hrec = equal_rect1 cmp f2 f1 f0 f l l0} in f13 __ __ hrec}
             in
             case compare27 t0 t1 of {
              EQ -> f14 __ __;
              _ -> f12 __}}}}}) (equal12 cmp m m')

equal_rec1 :: (a1 -> a1 -> Bool) -> ((T44 a1) -> (T44 a1) -> () -> () -> a2)
              -> ((T44 a1) -> (T44 a1) -> S11 -> a1 -> (List (Prod S11 a1))
              -> () -> S11 -> a1 -> (List (Prod S11 a1)) -> () -> () -> () ->
              a2 -> a2) -> ((T44 a1) -> (T44 a1) -> S11 -> a1 -> (List
              (Prod S11 a1)) -> () -> S11 -> a1 -> (List (Prod S11 a1)) -> ()
              -> (Compare S11) -> () -> () -> a2) -> ((T44 a1) -> (T44 
              a1) -> (T44 a1) -> () -> (T44 a1) -> () -> () -> a2) -> (T44
              a1) -> (T44 a1) -> a2
equal_rec1 =
  equal_rect1

r_equal_correct1 :: (a1 -> a1 -> Bool) -> (T44 a1) -> (T44 a1) -> Bool ->
                    R_equal1 a1
r_equal_correct1 cmp m m' _res =
  equal_rect1 cmp (\y y0 _ _ z _ -> eq_rect_r True (R_equal_8 y y0) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ ->
    eq_rect_r (andb (cmp y2 y6) (equal12 cmp y3 y7)) (R_equal_9 y y0 y1 y2 y3
      y5 y6 y7 (equal12 cmp y3 y7) (y11 (equal12 cmp y3 y7) __)) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ ->
    eq_rect_r False (R_equal_10 y y0 y1 y2 y3 y5 y6 y7 y9) z)
    (\y y0 y1 _ y3 _ _ z _ -> eq_rect_r False (R_equal_11 y y0 y1 y3) z) m m'
    _res __

map14 :: (a1 -> a2) -> (T44 a1) -> T44 a2
map14 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f e)) (map14 f m')}}

mapi6 :: (Key6 -> a1 -> a2) -> (T44 a1) -> T44 a2
mapi6 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f k e)) (mapi6 f m')}}

option_cons1 :: Key6 -> (Option a1) -> (List (Prod Key6 a1)) -> List
                (Prod Key6 a1)
option_cons1 k o l =
  case o of {
   Some e -> Cons (Pair k e) l;
   None -> l}

map2_l1 :: ((Option a1) -> (Option a2) -> Option a3) -> (T44 a1) -> T44 a3
map2_l1 f m =
  case m of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k e -> option_cons1 k (f (Some e) None) (map2_l1 f l)}}

map2_r1 :: ((Option a1) -> (Option a2) -> Option a3) -> (T44 a2) -> T44 a3
map2_r1 f m' =
  case m' of {
   Nil -> Nil;
   Cons p l' ->
    case p of {
     Pair k e' -> option_cons1 k (f None (Some e')) (map2_r1 f l')}}

map15 :: ((Option a1) -> (Option a2) -> Option a3) -> (T44 a1) -> (T44 
         a2) -> T44 a3
map15 f m =
  case m of {
   Nil -> map2_r1 f;
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       map2_aux m' =
         case m' of {
          Nil -> map2_l1 f m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare27 k k' of {
              LT -> option_cons1 k (f (Some e) None) (map15 f l m');
              EQ -> option_cons1 k (f (Some e) (Some e')) (map15 f l l');
              GT -> option_cons1 k' (f None (Some e')) (map2_aux l')}}}}
      in map2_aux}}

combine1 :: (T44 a1) -> (T44 a2) -> T44 (Prod (Option a1) (Option a2))
combine1 m =
  case m of {
   Nil -> map14 (\e' -> Pair None (Some e'));
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       combine_aux m' =
         case m' of {
          Nil -> map14 (\e0 -> Pair (Some e0) None) m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare27 k k' of {
              LT -> Cons (Pair k (Pair (Some e) None)) (combine1 l m');
              EQ -> Cons (Pair k (Pair (Some e) (Some e'))) (combine1 l l');
              GT -> Cons (Pair k' (Pair None (Some e'))) (combine_aux l')}}}}
      in combine_aux}}

fold_right_pair1 :: (a1 -> a2 -> a3 -> a3) -> (List (Prod a1 a2)) -> a3 -> a3
fold_right_pair1 f l i =
  fold_right (\p -> f (fst p) (snd p)) i l

map2_alt1 :: ((Option a1) -> (Option a2) -> Option a3) -> (T44 a1) -> (T44
             a2) -> List (Prod Key6 a3)
map2_alt1 f m m' =
  let {m0 = combine1 m m'} in
  let {m1 = map14 (\p -> f (fst p) (snd p)) m0} in
  fold_right_pair1 option_cons1 m1 Nil

at_least_one1 :: (Option a1) -> (Option a2) -> Option
                 (Prod (Option a1) (Option a2))
at_least_one1 o o' =
  case o of {
   Some _ -> Some (Pair o o');
   None -> case o' of {
            Some _ -> Some (Pair o o');
            None -> None}}

at_least_one_then_f1 :: ((Option a1) -> (Option a2) -> Option a3) -> (Option
                        a1) -> (Option a2) -> Option a3
at_least_one_then_f1 f o o' =
  case o of {
   Some _ -> f o o';
   None -> case o' of {
            Some _ -> f o o';
            None -> None}}

data R_mem4 elt =
   R_mem_20 (Tree3 elt)
 | R_mem_21 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T Bool (R_mem4 elt)
 | R_mem_22 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T
 | R_mem_23 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T Bool (R_mem4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect4 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
               a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () -> Bool
               -> (R_mem4 a1) -> a2 -> a2) -> ((Tree3 a1) -> (Tree3 a1) ->
               Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () -> a2) ->
               ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T ->
               () -> () -> () -> Bool -> (R_mem4 a1) -> a2 -> a2) -> (Tree3
               a1) -> Bool -> (R_mem4 a1) -> a2
r_mem_rect4 x f f0 f1 f2 _ _ r =
  case r of {
   R_mem_20 m -> f m __;
   R_mem_21 m l y _x r0 _x0 _res r1 ->
    f0 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect4 x f f0 f1 f2 l _res r1);
   R_mem_22 m l y _x r0 _x0 -> f1 m l y _x r0 _x0 __ __ __;
   R_mem_23 m l y _x r0 _x0 _res r1 ->
    f2 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect4 x f f0 f1 f2 r0 _res r1)}

r_mem_rec4 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
              a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () -> Bool
              -> (R_mem4 a1) -> a2 -> a2) -> ((Tree3 a1) -> (Tree3 a1) ->
              Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T ->
              () -> () -> () -> Bool -> (R_mem4 a1) -> a2 -> a2) -> (Tree3
              a1) -> Bool -> (R_mem4 a1) -> a2
r_mem_rec4 =
  r_mem_rect4

data R_find4 elt =
   R_find_20 (Tree3 elt)
 | R_find_21 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Option elt) 
 (R_find4 elt)
 | R_find_22 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T
 | R_find_23 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Option elt) 
 (R_find4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect4 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
                a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
                (Option a1) -> (R_find4 a1) -> a2 -> a2) -> ((Tree3 a1) ->
                (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> ()
                -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3
                a1) -> T -> () -> () -> () -> (Option a1) -> (R_find4 
                a1) -> a2 -> a2) -> (Tree3 a1) -> (Option a1) -> (R_find4 
                a1) -> a2
r_find_rect4 x f f0 f1 f2 _ _ r =
  case r of {
   R_find_20 m -> f m __;
   R_find_21 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_find_rect4 x f f0 f1 f2 l _res r1);
   R_find_22 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_find_23 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_find_rect4 x f f0 f1 f2 r0 _res r1)}

r_find_rec4 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
               a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
               (Option a1) -> (R_find4 a1) -> a2 -> a2) -> ((Tree3 a1) ->
               (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3
               a1) -> T -> () -> () -> () -> (Option a1) -> (R_find4 
               a1) -> a2 -> a2) -> (Tree3 a1) -> (Option a1) -> (R_find4 
               a1) -> a2
r_find_rec4 =
  r_find_rect4

data R_bal3 elt =
   R_bal_36 (Tree3 elt) Key5 elt (Tree3 elt)
 | R_bal_37 (Tree3 elt) Key5 elt (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T
 | R_bal_38 (Tree3 elt) Key5 elt (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T
 | R_bal_39 (Tree3 elt) Key5 elt (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T (Tree3 elt) Key5 elt (Tree3 elt) T
 | R_bal_40 (Tree3 elt) Key5 elt (Tree3 elt)
 | R_bal_41 (Tree3 elt) Key5 elt (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T
 | R_bal_42 (Tree3 elt) Key5 elt (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T
 | R_bal_43 (Tree3 elt) Key5 elt (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T (Tree3 elt) Key5 elt (Tree3 elt) T
 | R_bal_44 (Tree3 elt) Key5 elt (Tree3 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_bal_rect1 :: ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> () -> () ->
               a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> () ->
               (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> ()
               -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () ->
               () -> () -> a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 
               a1) -> () -> () -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 
               a1) -> T -> () -> () -> () -> (Tree3 a1) -> Key5 -> a1 ->
               (Tree3 a1) -> T -> () -> a2) -> ((Tree3 a1) -> Key5 -> a1 ->
               (Tree3 a1) -> () -> () -> () -> () -> () -> a2) -> ((Tree3 
               a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> () -> () -> () ->
               (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> ()
               -> () -> () -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T ->
               () -> () -> () -> () -> a2) -> ((Tree3 a1) -> Key5 -> a1 ->
               (Tree3 a1) -> () -> () -> () -> () -> (Tree3 a1) -> Key5 -> a1
               -> (Tree3 a1) -> T -> () -> () -> () -> (Tree3 a1) -> Key5 ->
               a1 -> (Tree3 a1) -> T -> () -> a2) -> ((Tree3 a1) -> Key5 ->
               a1 -> (Tree3 a1) -> () -> () -> () -> () -> a2) -> (Tree3 
               a1) -> Key5 -> a1 -> (Tree3 a1) -> (Tree3 a1) -> (R_bal3 
               a1) -> a2
r_bal_rect1 f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ r =
  case r of {
   R_bal_36 x x0 x1 x2 -> f x x0 x1 x2 __ __ __;
   R_bal_37 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_38 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_39 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_40 x x0 x1 x2 -> f3 x x0 x1 x2 __ __ __ __ __;
   R_bal_41 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_42 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_43 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_44 x x0 x1 x2 -> f7 x x0 x1 x2 __ __ __ __}

r_bal_rec1 :: ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> () -> () ->
              a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> () ->
              (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> ()
              -> a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> ()
              -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () ->
              () -> () -> a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 
              a1) -> () -> () -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T
              -> () -> () -> () -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 
              a1) -> T -> () -> a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3
              a1) -> () -> () -> () -> () -> () -> a2) -> ((Tree3 a1) -> Key5
              -> a1 -> (Tree3 a1) -> () -> () -> () -> () -> (Tree3 a1) ->
              Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> () -> () -> ()
              -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () ->
              () -> () -> a2) -> ((Tree3 a1) -> Key5 -> a1 -> (Tree3 
              a1) -> () -> () -> () -> () -> (Tree3 a1) -> Key5 -> a1 ->
              (Tree3 a1) -> T -> () -> () -> () -> (Tree3 a1) -> Key5 -> a1
              -> (Tree3 a1) -> T -> () -> a2) -> ((Tree3 a1) -> Key5 -> a1 ->
              (Tree3 a1) -> () -> () -> () -> () -> a2) -> (Tree3 a1) -> Key5
              -> a1 -> (Tree3 a1) -> (Tree3 a1) -> (R_bal3 a1) -> a2
r_bal_rec1 =
  r_bal_rect1

data R_add4 elt =
   R_add_20 (Tree3 elt)
 | R_add_21 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Tree3 elt) 
 (R_add4 elt)
 | R_add_22 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T
 | R_add_23 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Tree3 elt) 
 (R_add4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect4 :: Key5 -> a1 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) ->
               (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> ()
               -> (Tree3 a1) -> (R_add4 a1) -> a2 -> a2) -> ((Tree3 a1) ->
               (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3
               a1) -> T -> () -> () -> () -> (Tree3 a1) -> (R_add4 a1) -> a2
               -> a2) -> (Tree3 a1) -> (Tree3 a1) -> (R_add4 a1) -> a2
r_add_rect4 x d f f0 f1 f2 _ _ r =
  case r of {
   R_add_20 m -> f m __;
   R_add_21 m l y d' r0 h _res r1 ->
    f0 m l y d' r0 h __ __ __ _res r1 (r_add_rect4 x d f f0 f1 f2 l _res r1);
   R_add_22 m l y d' r0 h -> f1 m l y d' r0 h __ __ __;
   R_add_23 m l y d' r0 h _res r1 ->
    f2 m l y d' r0 h __ __ __ _res r1 (r_add_rect4 x d f f0 f1 f2 r0 _res r1)}

r_add_rec4 :: Key5 -> a1 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3
              a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
              (Tree3 a1) -> (R_add4 a1) -> a2 -> a2) -> ((Tree3 a1) -> (Tree3
              a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () -> a2)
              -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T
              -> () -> () -> () -> (Tree3 a1) -> (R_add4 a1) -> a2 -> a2) ->
              (Tree3 a1) -> (Tree3 a1) -> (R_add4 a1) -> a2
r_add_rec4 =
  r_add_rect4

data R_remove_min3 elt =
   R_remove_min_8 (Tree3 elt) Key5 elt (Tree3 elt)
 | R_remove_min_9 (Tree3 elt) Key5 elt (Tree3 elt) (Tree3 elt) Key5 elt 
 (Tree3 elt) T (Prod (Tree3 elt) (Prod Key5 elt)) (R_remove_min3 elt) 
 (Tree3 elt) (Prod Key5 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_min_rect1 :: ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> a2) ->
                      ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> (Tree3 
                      a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Prod
                      (Tree3 a1) (Prod Key5 a1)) -> (R_remove_min3 a1) -> a2
                      -> (Tree3 a1) -> (Prod Key5 a1) -> () -> a2) -> (Tree3
                      a1) -> Key5 -> a1 -> (Tree3 a1) -> (Prod (Tree3 a1)
                      (Prod Key5 a1)) -> (R_remove_min3 a1) -> a2
r_remove_min_rect1 f f0 _ _ _ _ _ r =
  case r of {
   R_remove_min_8 l x d r0 -> f l x d r0 __;
   R_remove_min_9 l x d r0 ll lx ld lr _x _res r1 l' m ->
    f0 l x d r0 ll lx ld lr _x __ _res r1
      (r_remove_min_rect1 f f0 ll lx ld lr _res r1) l' m __}

r_remove_min_rec1 :: ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> () -> a2) ->
                     ((Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> (Tree3 
                     a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Prod
                     (Tree3 a1) (Prod Key5 a1)) -> (R_remove_min3 a1) -> a2
                     -> (Tree3 a1) -> (Prod Key5 a1) -> () -> a2) -> (Tree3
                     a1) -> Key5 -> a1 -> (Tree3 a1) -> (Prod (Tree3 a1)
                     (Prod Key5 a1)) -> (R_remove_min3 a1) -> a2
r_remove_min_rec1 =
  r_remove_min_rect1

data R_merge3 elt =
   R_merge_12 (Tree3 elt) (Tree3 elt)
 | R_merge_13 (Tree3 elt) (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T
 | R_merge_14 (Tree3 elt) (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T (Tree3 elt) Key5 elt (Tree3 elt) T (Tree3 elt) (Prod Key5 elt) Key5 
 elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_merge_rect1 :: ((Tree3 a1) -> (Tree3 a1) -> () -> a2) -> ((Tree3 a1) ->
                 (Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T ->
                 () -> () -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> (Tree3 
                 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                 a1) -> (Prod Key5 a1) -> () -> Key5 -> a1 -> () -> a2) ->
                 (Tree3 a1) -> (Tree3 a1) -> (Tree3 a1) -> (R_merge3 
                 a1) -> a2
r_merge_rect1 f f0 f1 _ _ _ r =
  case r of {
   R_merge_12 x x0 -> f x x0 __;
   R_merge_13 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_merge_14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __}

r_merge_rec1 :: ((Tree3 a1) -> (Tree3 a1) -> () -> a2) -> ((Tree3 a1) ->
                (Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T ->
                () -> () -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> (Tree3 
                a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                a1) -> (Prod Key5 a1) -> () -> Key5 -> a1 -> () -> a2) ->
                (Tree3 a1) -> (Tree3 a1) -> (Tree3 a1) -> (R_merge3 a1) -> a2
r_merge_rec1 =
  r_merge_rect1

data R_remove4 elt =
   R_remove_20 (Tree3 elt)
 | R_remove_21 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Tree3 elt) 
 (R_remove4 elt)
 | R_remove_22 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T
 | R_remove_23 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Tree3 elt) 
 (R_remove4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect4 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3
                  a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
                  (Tree3 a1) -> (R_remove4 a1) -> a2 -> a2) -> ((Tree3 
                  a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () ->
                  () -> () -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1
                  -> (Tree3 a1) -> T -> () -> () -> () -> (Tree3 a1) ->
                  (R_remove4 a1) -> a2 -> a2) -> (Tree3 a1) -> (Tree3 
                  a1) -> (R_remove4 a1) -> a2
r_remove_rect4 x f f0 f1 f2 _ _ r =
  case r of {
   R_remove_20 m -> f m __;
   R_remove_21 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_remove_rect4 x f f0 f1 f2 l _res r1);
   R_remove_22 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_remove_23 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1
      (r_remove_rect4 x f f0 f1 f2 r0 _res r1)}

r_remove_rec4 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
                 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
                 (Tree3 a1) -> (R_remove4 a1) -> a2 -> a2) -> ((Tree3 
                 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () ->
                 () -> () -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1
                 -> (Tree3 a1) -> T -> () -> () -> () -> (Tree3 a1) ->
                 (R_remove4 a1) -> a2 -> a2) -> (Tree3 a1) -> (Tree3 
                 a1) -> (R_remove4 a1) -> a2
r_remove_rec4 =
  r_remove_rect4

data R_concat3 elt =
   R_concat_12 (Tree3 elt) (Tree3 elt)
 | R_concat_13 (Tree3 elt) (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T
 | R_concat_14 (Tree3 elt) (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) 
 T (Tree3 elt) Key5 elt (Tree3 elt) T (Tree3 elt) (Prod Key5 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_concat_rect1 :: ((Tree3 a1) -> (Tree3 a1) -> () -> a2) -> ((Tree3 a1) ->
                  (Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T
                  -> () -> () -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> (Tree3
                  a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                  a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                  a1) -> (Prod Key5 a1) -> () -> a2) -> (Tree3 a1) -> (Tree3
                  a1) -> (Tree3 a1) -> (R_concat3 a1) -> a2
r_concat_rect1 f f0 f1 _ _ _ r =
  case r of {
   R_concat_12 x x0 -> f x x0 __;
   R_concat_13 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_concat_14 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __}

r_concat_rec1 :: ((Tree3 a1) -> (Tree3 a1) -> () -> a2) -> ((Tree3 a1) ->
                 (Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T ->
                 () -> () -> a2) -> ((Tree3 a1) -> (Tree3 a1) -> (Tree3 
                 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                 a1) -> (Prod Key5 a1) -> () -> a2) -> (Tree3 a1) -> (Tree3
                 a1) -> (Tree3 a1) -> (R_concat3 a1) -> a2
r_concat_rec1 =
  r_concat_rect1

data R_split1 elt =
   R_split_8 (Tree3 elt)
 | R_split_9 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Triple3 elt) 
 (R_split1 elt) (Tree3 elt) (Option elt) (Tree3 elt)
 | R_split_10 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T
 | R_split_11 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Triple3 elt) 
 (R_split1 elt) (Tree3 elt) (Option elt) (Tree3 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_split_rect1 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
                 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
                 (Triple3 a1) -> (R_split1 a1) -> a2 -> (Tree3 a1) -> (Option
                 a1) -> (Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
                 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
                 a2) -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 
                 a1) -> T -> () -> () -> () -> (Triple3 a1) -> (R_split1 
                 a1) -> a2 -> (Tree3 a1) -> (Option a1) -> (Tree3 a1) -> ()
                 -> a2) -> (Tree3 a1) -> (Triple3 a1) -> (R_split1 a1) -> a2
r_split_rect1 x f f0 f1 f2 _ _ r =
  case r of {
   R_split_8 m -> f m __;
   R_split_9 m l y d r0 _x _res r1 ll o rl ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_split_rect1 x f f0 f1 f2 l _res r1)
      ll o rl __;
   R_split_10 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_split_11 m l y d r0 _x _res r1 rl o rr ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_split_rect1 x f f0 f1 f2 r0 _res r1)
      rl o rr __}

r_split_rec1 :: S11 -> ((Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
                a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () ->
                (Triple3 a1) -> (R_split1 a1) -> a2 -> (Tree3 a1) -> (Option
                a1) -> (Tree3 a1) -> () -> a2) -> ((Tree3 a1) -> (Tree3 
                a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> () -> () -> a2)
                -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 
                a1) -> T -> () -> () -> () -> (Triple3 a1) -> (R_split1 
                a1) -> a2 -> (Tree3 a1) -> (Option a1) -> (Tree3 a1) -> () ->
                a2) -> (Tree3 a1) -> (Triple3 a1) -> (R_split1 a1) -> a2
r_split_rec1 =
  r_split_rect1

data R_map_option1 elt x =
   R_map_option_6 (Tree3 elt)
 | R_map_option_7 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T x (Tree3 x) 
 (R_map_option1 elt x) (Tree3 x) (R_map_option1 elt x)
 | R_map_option_8 (Tree3 elt) (Tree3 elt) Key5 elt (Tree3 elt) T (Tree3 x) 
 (R_map_option1 elt x) (Tree3 x) (R_map_option1 elt x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map_option_rect1 :: (Key5 -> a1 -> Option a2) -> ((Tree3 a1) -> () -> a3)
                      -> ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3
                      a1) -> T -> () -> a2 -> () -> (Tree3 a2) ->
                      (R_map_option1 a1 a2) -> a3 -> (Tree3 a2) ->
                      (R_map_option1 a1 a2) -> a3 -> a3) -> ((Tree3 a1) ->
                      (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> ()
                      -> (Tree3 a2) -> (R_map_option1 a1 a2) -> a3 -> (Tree3
                      a2) -> (R_map_option1 a1 a2) -> a3 -> a3) -> (Tree3 
                      a1) -> (Tree3 a2) -> (R_map_option1 a1 a2) -> a3
r_map_option_rect1 f f0 f1 f2 _ _ r =
  case r of {
   R_map_option_6 m -> f0 m __;
   R_map_option_7 m l x d r0 _x d' _res0 r1 _res r2 ->
    f1 m l x d r0 _x __ d' __ _res0 r1
      (r_map_option_rect1 f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect1 f f0 f1 f2 r0 _res r2);
   R_map_option_8 m l x d r0 _x _res0 r1 _res r2 ->
    f2 m l x d r0 _x __ __ _res0 r1
      (r_map_option_rect1 f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect1 f f0 f1 f2 r0 _res r2)}

r_map_option_rec1 :: (Key5 -> a1 -> Option a2) -> ((Tree3 a1) -> () -> a3) ->
                     ((Tree3 a1) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 
                     a1) -> T -> () -> a2 -> () -> (Tree3 a2) ->
                     (R_map_option1 a1 a2) -> a3 -> (Tree3 a2) ->
                     (R_map_option1 a1 a2) -> a3 -> a3) -> ((Tree3 a1) ->
                     (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> ()
                     -> (Tree3 a2) -> (R_map_option1 a1 a2) -> a3 -> (Tree3
                     a2) -> (R_map_option1 a1 a2) -> a3 -> a3) -> (Tree3 
                     a1) -> (Tree3 a2) -> (R_map_option1 a1 a2) -> a3
r_map_option_rec1 =
  r_map_option_rect1

data R_map2_opt1 elt x0 x =
   R_map2_opt_8 (Tree3 elt) (Tree3 x0)
 | R_map2_opt_9 (Tree3 elt) (Tree3 x0) (Tree3 elt) Key5 elt (Tree3 elt) 
 T
 | R_map2_opt_10 (Tree3 elt) (Tree3 x0) (Tree3 elt) Key5 elt (Tree3 elt) 
 T (Tree3 x0) Key5 x0 (Tree3 x0) T (Tree3 x0) (Option x0) (Tree3 x0) 
 x (Tree3 x) (R_map2_opt1 elt x0 x) (Tree3 x) (R_map2_opt1 elt x0 x)
 | R_map2_opt_11 (Tree3 elt) (Tree3 x0) (Tree3 elt) Key5 elt (Tree3 elt) 
 T (Tree3 x0) Key5 x0 (Tree3 x0) T (Tree3 x0) (Option x0) (Tree3 x0) 
 (Tree3 x) (R_map2_opt1 elt x0 x) (Tree3 x) (R_map2_opt1 elt x0 x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map2_opt_rect1 :: (Key5 -> a1 -> (Option a2) -> Option a3) -> ((Tree3 
                    a1) -> Tree3 a3) -> ((Tree3 a2) -> Tree3 a3) -> ((Tree3
                    a1) -> (Tree3 a2) -> () -> a4) -> ((Tree3 a1) -> (Tree3
                    a2) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> ()
                    -> () -> a4) -> ((Tree3 a1) -> (Tree3 a2) -> (Tree3 
                    a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                    a2) -> Key5 -> a2 -> (Tree3 a2) -> T -> () -> (Tree3 
                    a2) -> (Option a2) -> (Tree3 a2) -> () -> a3 -> () ->
                    (Tree3 a3) -> (R_map2_opt1 a1 a2 a3) -> a4 -> (Tree3 
                    a3) -> (R_map2_opt1 a1 a2 a3) -> a4 -> a4) -> ((Tree3 
                    a1) -> (Tree3 a2) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3
                    a1) -> T -> () -> (Tree3 a2) -> Key5 -> a2 -> (Tree3 
                    a2) -> T -> () -> (Tree3 a2) -> (Option a2) -> (Tree3 
                    a2) -> () -> () -> (Tree3 a3) -> (R_map2_opt1 a1 
                    a2 a3) -> a4 -> (Tree3 a3) -> (R_map2_opt1 a1 a2 
                    a3) -> a4 -> a4) -> (Tree3 a1) -> (Tree3 a2) -> (Tree3
                    a3) -> (R_map2_opt1 a1 a2 a3) -> a4
r_map2_opt_rect1 f mapl mapr f0 f1 f2 f3 _ _ _ r =
  case r of {
   R_map2_opt_8 m1 m2 -> f0 m1 m2 __;
   R_map2_opt_9 m1 m2 l1 x1 d1 r1 _x -> f1 m1 m2 l1 x1 d1 r1 _x __ __;
   R_map2_opt_10 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' e _res0
    r0 _res r2 ->
    f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
      _res0 r0 (r_map2_opt_rect1 f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
      _res r2 (r_map2_opt_rect1 f mapl mapr f0 f1 f2 f3 r1 r2' _res r2);
   R_map2_opt_11 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' _res0 r0
    _res r2 ->
    f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
      r0 (r_map2_opt_rect1 f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
      (r_map2_opt_rect1 f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)}

r_map2_opt_rec1 :: (Key5 -> a1 -> (Option a2) -> Option a3) -> ((Tree3 
                   a1) -> Tree3 a3) -> ((Tree3 a2) -> Tree3 a3) -> ((Tree3
                   a1) -> (Tree3 a2) -> () -> a4) -> ((Tree3 a1) -> (Tree3
                   a2) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> ()
                   -> () -> a4) -> ((Tree3 a1) -> (Tree3 a2) -> (Tree3 
                   a1) -> Key5 -> a1 -> (Tree3 a1) -> T -> () -> (Tree3 
                   a2) -> Key5 -> a2 -> (Tree3 a2) -> T -> () -> (Tree3 
                   a2) -> (Option a2) -> (Tree3 a2) -> () -> a3 -> () ->
                   (Tree3 a3) -> (R_map2_opt1 a1 a2 a3) -> a4 -> (Tree3 
                   a3) -> (R_map2_opt1 a1 a2 a3) -> a4 -> a4) -> ((Tree3 
                   a1) -> (Tree3 a2) -> (Tree3 a1) -> Key5 -> a1 -> (Tree3
                   a1) -> T -> () -> (Tree3 a2) -> Key5 -> a2 -> (Tree3 
                   a2) -> T -> () -> (Tree3 a2) -> (Option a2) -> (Tree3 
                   a2) -> () -> () -> (Tree3 a3) -> (R_map2_opt1 a1 a2 
                   a3) -> a4 -> (Tree3 a3) -> (R_map2_opt1 a1 a2 a3) -> a4 ->
                   a4) -> (Tree3 a1) -> (Tree3 a2) -> (Tree3 a3) ->
                   (R_map2_opt1 a1 a2 a3) -> a4
r_map2_opt_rec1 =
  r_map2_opt_rect1

fold'1 :: (Key5 -> a1 -> a2 -> a2) -> (Tree3 a1) -> a2 -> a2
fold'1 f s =
  fold12 f (elements11 s)

flatten_e3 :: (Enumeration3 a1) -> List (Prod Key5 a1)
flatten_e3 e =
  case e of {
   End3 -> Nil;
   More3 x e0 t r -> Cons (Pair x e0) (app (elements11 t) (flatten_e3 r))}

type Bst1 elt = Tree3 elt
  -- singleton inductive, whose constructor was Bst
  
this3 :: (Bst1 a1) -> Tree3 a1
this3 b =
  b

type T45 elt = Bst1 elt

type Key7 = S11

empty13 :: T45 a1
empty13 =
  empty11

is_empty13 :: (T45 a1) -> Bool
is_empty13 m =
  is_empty11 (this3 m)

add16 :: Key7 -> a1 -> (T45 a1) -> T45 a1
add16 x e m =
  add14 x e (this3 m)

remove13 :: Key7 -> (T45 a1) -> T45 a1
remove13 x m =
  remove11 x (this3 m)

mem13 :: Key7 -> (T45 a1) -> Bool
mem13 x m =
  mem11 x (this3 m)

find7 :: Key7 -> (T45 a1) -> Option a1
find7 x m =
  find5 x (this3 m)

map16 :: (a1 -> a2) -> (T45 a1) -> T45 a2
map16 f m =
  map12 f (this3 m)

mapi7 :: (Key7 -> a1 -> a2) -> (T45 a1) -> T45 a2
mapi7 f m =
  mapi5 f (this3 m)

map17 :: ((Option a1) -> (Option a2) -> Option a3) -> (T45 a1) -> (T45 
         a2) -> T45 a3
map17 f m m' =
  map13 f (this3 m) (this3 m')

elements13 :: (T45 a1) -> List (Prod Key7 a1)
elements13 m =
  elements11 (this3 m)

cardinal10 :: (T45 a1) -> Nat
cardinal10 m =
  cardinal9 (this3 m)

fold13 :: (Key7 -> a1 -> a2 -> a2) -> (T45 a1) -> a2 -> a2
fold13 f m i =
  fold11 f (this3 m) i

equal13 :: (a1 -> a1 -> Bool) -> (T45 a1) -> (T45 a1) -> Bool
equal13 cmp m m' =
  equal11 cmp (this3 m) (this3 m')

emptySCMap :: T45 CCStatus
emptySCMap =
  empty13

type SC_MAP_TYPE = T45 CCStatus

type S13 = Prod IdentChoiceT Person

type S14 = S13

st7 :: S14 -> List Prelude.Integer
st7 x =
  case x of {
   Pair i p -> Cons i (Cons p Nil)}

type T46 = S14

compareList7 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList7 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec7 :: T46 -> T46 -> Sumor Sumbool
compareDec7 x y =
  compareList7 (case x of {
                 Pair i p -> Cons i (Cons p Nil)})
    (case y of {
      Pair i p -> Cons i (Cons p Nil)})

compare29 :: T46 -> T46 -> Compare T46
compare29 x y =
  let {h = compareDec7 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec43 :: T46 -> T46 -> Sumbool
eq_dec43 x y =
  let {h = compareDec7 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type S15 = S13

st8 :: S15 -> List Prelude.Integer
st8 x =
  case x of {
   Pair i p -> Cons i (Cons p Nil)}

type T47 = S15

compareList8 :: (List Prelude.Integer) -> (List Prelude.Integer) -> Sumor
                Sumbool
compareList8 x y =
  doubleInduction (\y0 ->
    case y0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inleft Left}) (\x0 ->
    case x0 of {
     Nil -> Inleft Right;
     Cons _ _ -> Inright}) (\x0 y0 _ _ h ->
    let {h0 = compareZdec x0 y0} in
    case h0 of {
     Inleft s0 -> case s0 of {
                   Left -> Inleft Left;
                   Right -> h};
     Inright -> Inright}) x y

compareDec8 :: T47 -> T47 -> Sumor Sumbool
compareDec8 x y =
  compareList8 (case x of {
                 Pair i p -> Cons i (Cons p Nil)})
    (case y of {
      Pair i p -> Cons i (Cons p Nil)})

compare30 :: T47 -> T47 -> Compare T47
compare30 x y =
  let {h = compareDec8 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> LT;
                 Right -> EQ};
   Inright -> GT}

eq_dec44 :: T47 -> T47 -> Sumbool
eq_dec44 x y =
  let {h = compareDec8 x y} in
  case h of {
   Inleft s0 -> case s0 of {
                 Left -> Right;
                 Right -> Left};
   Inright -> Right}

type Key8 = S14

data Tree4 elt =
   Leaf4
 | Node4 (Tree4 elt) Key8 elt (Tree4 elt) T
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

tree_rect2 :: a2 -> ((Tree4 a1) -> a2 -> Key8 -> a1 -> (Tree4 a1) -> a2 -> T
              -> a2) -> (Tree4 a1) -> a2
tree_rect2 f f0 t =
  case t of {
   Leaf4 -> f;
   Node4 t0 k e t1 t2 ->
    f0 t0 (tree_rect2 f f0 t0) k e t1 (tree_rect2 f f0 t1) t2}

tree_rec2 :: a2 -> ((Tree4 a1) -> a2 -> Key8 -> a1 -> (Tree4 a1) -> a2 -> T
             -> a2) -> (Tree4 a1) -> a2
tree_rec2 =
  tree_rect2

height4 :: (Tree4 a1) -> T
height4 m =
  case m of {
   Leaf4 -> _0;
   Node4 _ _ _ _ h -> h}

cardinal11 :: (Tree4 a1) -> Nat
cardinal11 m =
  case m of {
   Leaf4 -> O;
   Node4 l _ _ r _ -> S (add (cardinal11 l) (cardinal11 r))}

empty14 :: Tree4 a1
empty14 =
  Leaf4

is_empty14 :: (Tree4 a1) -> Bool
is_empty14 m =
  case m of {
   Leaf4 -> True;
   Node4 _ _ _ _ _ -> False}

mem14 :: S14 -> (Tree4 a1) -> Bool
mem14 x m =
  case m of {
   Leaf4 -> False;
   Node4 l y _ r _ ->
    case compare29 x y of {
     LT -> mem14 x l;
     EQ -> True;
     GT -> mem14 x r}}

find8 :: S14 -> (Tree4 a1) -> Option a1
find8 x m =
  case m of {
   Leaf4 -> None;
   Node4 l y d r _ ->
    case compare29 x y of {
     LT -> find8 x l;
     EQ -> Some d;
     GT -> find8 x r}}

create4 :: (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> Tree4 a1
create4 l x e r =
  Node4 l x e r (add1 (max0 (height4 l) (height4 r)) _1)

assert_false4 :: (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> Tree4 a1
assert_false4 =
  create4

bal4 :: (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> Tree4 a1
bal4 l x d r =
  let {hl = height4 l} in
  let {hr = height4 r} in
  case gt_le_dec hl (add1 hr _2) of {
   Left ->
    case l of {
     Leaf4 -> assert_false4 l x d r;
     Node4 ll lx ld lr _ ->
      case ge_lt_dec (height4 ll) (height4 lr) of {
       Left -> create4 ll lx ld (create4 lr x d r);
       Right ->
        case lr of {
         Leaf4 -> assert_false4 l x d r;
         Node4 lrl lrx lrd lrr _ ->
          create4 (create4 ll lx ld lrl) lrx lrd (create4 lrr x d r)}}};
   Right ->
    case gt_le_dec hr (add1 hl _2) of {
     Left ->
      case r of {
       Leaf4 -> assert_false4 l x d r;
       Node4 rl rx rd rr _ ->
        case ge_lt_dec (height4 rr) (height4 rl) of {
         Left -> create4 (create4 l x d rl) rx rd rr;
         Right ->
          case rl of {
           Leaf4 -> assert_false4 l x d r;
           Node4 rll rlx rld rlr _ ->
            create4 (create4 l x d rll) rlx rld (create4 rlr rx rd rr)}}};
     Right -> create4 l x d r}}

add17 :: Key8 -> a1 -> (Tree4 a1) -> Tree4 a1
add17 x d m =
  case m of {
   Leaf4 -> Node4 Leaf4 x d Leaf4 _1;
   Node4 l y d' r h ->
    case compare29 x y of {
     LT -> bal4 (add17 x d l) y d' r;
     EQ -> Node4 l y d r h;
     GT -> bal4 l y d' (add17 x d r)}}

remove_min4 :: (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> Prod (Tree4 a1)
               (Prod Key8 a1)
remove_min4 l x d r =
  case l of {
   Leaf4 -> Pair r (Pair x d);
   Node4 ll lx ld lr _ ->
    case remove_min4 ll lx ld lr of {
     Pair l' m -> Pair (bal4 l' x d r) m}}

merge4 :: (Tree4 a1) -> (Tree4 a1) -> Tree4 a1
merge4 s1 s2 =
  case s1 of {
   Leaf4 -> s2;
   Node4 _ _ _ _ _ ->
    case s2 of {
     Leaf4 -> s1;
     Node4 l2 x2 d2 r2 _ ->
      case remove_min4 l2 x2 d2 r2 of {
       Pair s2' p -> case p of {
                      Pair x d -> bal4 s1 x d s2'}}}}

remove14 :: S14 -> (Tree4 a1) -> Tree4 a1
remove14 x m =
  case m of {
   Leaf4 -> Leaf4;
   Node4 l y d r _ ->
    case compare29 x y of {
     LT -> bal4 (remove14 x l) y d r;
     EQ -> merge4 l r;
     GT -> bal4 l y d (remove14 x r)}}

join4 :: (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> Tree4 a1
join4 l =
  case l of {
   Leaf4 -> add17;
   Node4 ll lx ld lr lh -> (\x d ->
    let {
     join_aux r =
       case r of {
        Leaf4 -> add17 x d l;
        Node4 rl rx rd rr rh ->
         case gt_le_dec lh (add1 rh _2) of {
          Left -> bal4 ll lx ld (join4 lr x d r);
          Right ->
           case gt_le_dec rh (add1 lh _2) of {
            Left -> bal4 (join_aux rl) rx rd rr;
            Right -> create4 l x d r}}}}
    in join_aux)}

data Triple4 elt =
   Mktriple4 (Tree4 elt) (Option elt) (Tree4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

t_left4 :: (Triple4 a1) -> Tree4 a1
t_left4 t =
  case t of {
   Mktriple4 t_left5 _ _ -> t_left5}

t_opt2 :: (Triple4 a1) -> Option a1
t_opt2 t =
  case t of {
   Mktriple4 _ t_opt3 _ -> t_opt3}

t_right4 :: (Triple4 a1) -> Tree4 a1
t_right4 t =
  case t of {
   Mktriple4 _ _ t_right5 -> t_right5}

split4 :: S14 -> (Tree4 a1) -> Triple4 a1
split4 x m =
  case m of {
   Leaf4 -> Mktriple4 Leaf4 None Leaf4;
   Node4 l y d r _ ->
    case compare29 x y of {
     LT ->
      case split4 x l of {
       Mktriple4 ll o rl -> Mktriple4 ll o (join4 rl y d r)};
     EQ -> Mktriple4 l (Some d) r;
     GT ->
      case split4 x r of {
       Mktriple4 rl o rr -> Mktriple4 (join4 l y d rl) o rr}}}

concat4 :: (Tree4 a1) -> (Tree4 a1) -> Tree4 a1
concat4 m1 m2 =
  case m1 of {
   Leaf4 -> m2;
   Node4 _ _ _ _ _ ->
    case m2 of {
     Leaf4 -> m1;
     Node4 l2 x2 d2 r2 _ ->
      case remove_min4 l2 x2 d2 r2 of {
       Pair m2' xd -> join4 m1 (fst xd) (snd xd) m2'}}}

elements_aux4 :: (List (Prod Key8 a1)) -> (Tree4 a1) -> List (Prod Key8 a1)
elements_aux4 acc m =
  case m of {
   Leaf4 -> acc;
   Node4 l x d r _ -> elements_aux4 (Cons (Pair x d) (elements_aux4 acc r)) l}

elements14 :: (Tree4 a1) -> List (Prod Key8 a1)
elements14 =
  elements_aux4 Nil

fold14 :: (Key8 -> a1 -> a2 -> a2) -> (Tree4 a1) -> a2 -> a2
fold14 f m a =
  case m of {
   Leaf4 -> a;
   Node4 l x d r _ -> fold14 f r (f x d (fold14 f l a))}

data Enumeration4 elt =
   End4
 | More4 Key8 elt (Tree4 elt) (Enumeration4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

enumeration_rect2 :: a2 -> (Key8 -> a1 -> (Tree4 a1) -> (Enumeration4 
                     a1) -> a2 -> a2) -> (Enumeration4 a1) -> a2
enumeration_rect2 f f0 e =
  case e of {
   End4 -> f;
   More4 k e0 t e1 -> f0 k e0 t e1 (enumeration_rect2 f f0 e1)}

enumeration_rec2 :: a2 -> (Key8 -> a1 -> (Tree4 a1) -> (Enumeration4 
                    a1) -> a2 -> a2) -> (Enumeration4 a1) -> a2
enumeration_rec2 =
  enumeration_rect2

cons4 :: (Tree4 a1) -> (Enumeration4 a1) -> Enumeration4 a1
cons4 m e =
  case m of {
   Leaf4 -> e;
   Node4 l x d r _ -> cons4 l (More4 x d r e)}

equal_more2 :: (a1 -> a1 -> Bool) -> S14 -> a1 -> ((Enumeration4 a1) -> Bool)
               -> (Enumeration4 a1) -> Bool
equal_more2 cmp x1 d1 cont e2 =
  case e2 of {
   End4 -> False;
   More4 x2 d2 r2 e3 ->
    case compare29 x1 x2 of {
     EQ -> case cmp d1 d2 of {
            True -> cont (cons4 r2 e3);
            False -> False};
     _ -> False}}

equal_cont2 :: (a1 -> a1 -> Bool) -> (Tree4 a1) -> ((Enumeration4 a1) ->
               Bool) -> (Enumeration4 a1) -> Bool
equal_cont2 cmp m1 cont e2 =
  case m1 of {
   Leaf4 -> cont e2;
   Node4 l1 x1 d1 r1 _ ->
    equal_cont2 cmp l1 (equal_more2 cmp x1 d1 (equal_cont2 cmp r1 cont)) e2}

equal_end2 :: (Enumeration4 a1) -> Bool
equal_end2 e2 =
  case e2 of {
   End4 -> True;
   More4 _ _ _ _ -> False}

equal14 :: (a1 -> a1 -> Bool) -> (Tree4 a1) -> (Tree4 a1) -> Bool
equal14 cmp m1 m2 =
  equal_cont2 cmp m1 equal_end2 (cons4 m2 End4)

map18 :: (a1 -> a2) -> (Tree4 a1) -> Tree4 a2
map18 f m =
  case m of {
   Leaf4 -> Leaf4;
   Node4 l x d r h -> Node4 (map18 f l) x (f d) (map18 f r) h}

mapi8 :: (Key8 -> a1 -> a2) -> (Tree4 a1) -> Tree4 a2
mapi8 f m =
  case m of {
   Leaf4 -> Leaf4;
   Node4 l x d r h -> Node4 (mapi8 f l) x (f x d) (mapi8 f r) h}

map_option2 :: (Key8 -> a1 -> Option a2) -> (Tree4 a1) -> Tree4 a2
map_option2 f m =
  case m of {
   Leaf4 -> Leaf4;
   Node4 l x d r _ ->
    case f x d of {
     Some d' -> join4 (map_option2 f l) x d' (map_option2 f r);
     None -> concat4 (map_option2 f l) (map_option2 f r)}}

map2_opt2 :: (Key8 -> a1 -> (Option a2) -> Option a3) -> ((Tree4 a1) -> Tree4
             a3) -> ((Tree4 a2) -> Tree4 a3) -> (Tree4 a1) -> (Tree4 
             a2) -> Tree4 a3
map2_opt2 f mapl mapr m1 m2 =
  case m1 of {
   Leaf4 -> mapr m2;
   Node4 l1 x1 d1 r1 _ ->
    case m2 of {
     Leaf4 -> mapl m1;
     Node4 _ _ _ _ _ ->
      case split4 x1 m2 of {
       Mktriple4 l2' o2 r2' ->
        case f x1 d1 o2 of {
         Some e ->
          join4 (map2_opt2 f mapl mapr l1 l2') x1 e
            (map2_opt2 f mapl mapr r1 r2');
         None ->
          concat4 (map2_opt2 f mapl mapr l1 l2')
            (map2_opt2 f mapl mapr r1 r2')}}}}

map19 :: ((Option a1) -> (Option a2) -> Option a3) -> (Tree4 a1) -> (Tree4
         a2) -> Tree4 a3
map19 f =
  map2_opt2 (\_ d o -> f (Some d) o) (map_option2 (\_ d -> f (Some d) None))
    (map_option2 (\_ d' -> f None (Some d')))

type T48 = S14

eq_dec45 :: S14 -> S14 -> Sumbool
eq_dec45 =
  eq_dec43

lt_dec15 :: S14 -> S14 -> Sumbool
lt_dec15 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare29 x y)

eqb19 :: S14 -> S14 -> Bool
eqb19 x y =
  case eq_dec45 x y of {
   Left -> True;
   Right -> False}

type T49 = S14

eq_dec46 :: S14 -> S14 -> Sumbool
eq_dec46 =
  eq_dec43

lt_dec16 :: S14 -> S14 -> Sumbool
lt_dec16 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare29 x y)

eqb20 :: S14 -> S14 -> Bool
eqb20 x y =
  case eq_dec46 x y of {
   Left -> True;
   Right -> False}

type T50 = S14

eq_dec47 :: S14 -> S14 -> Sumbool
eq_dec47 =
  eq_dec43

lt_dec17 :: S14 -> S14 -> Sumbool
lt_dec17 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare29 x y)

eqb21 :: S14 -> S14 -> Bool
eqb21 x y =
  case eq_dec47 x y of {
   Left -> True;
   Right -> False}

type T51 = S14

eq_dec48 :: S14 -> S14 -> Sumbool
eq_dec48 =
  eq_dec43

lt_dec18 :: S14 -> S14 -> Sumbool
lt_dec18 x y =
  compare_rec x y (\_ -> Left) (\_ -> Right) (\_ -> Right) (compare29 x y)

eqb22 :: S14 -> S14 -> Bool
eqb22 x y =
  case eq_dec48 x y of {
   Left -> True;
   Right -> False}

type Key9 = S14

type T52 elt = List (Prod S14 elt)

empty15 :: T52 a1
empty15 =
  Nil

is_empty15 :: (T52 a1) -> Bool
is_empty15 l =
  case l of {
   Nil -> True;
   Cons _ _ -> False}

mem15 :: Key9 -> (T52 a1) -> Bool
mem15 k s =
  case s of {
   Nil -> False;
   Cons p l ->
    case p of {
     Pair k' _ ->
      case compare29 k k' of {
       LT -> False;
       EQ -> True;
       GT -> mem15 k l}}}

data R_mem5 elt =
   R_mem_24 (T52 elt)
 | R_mem_25 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_mem_26 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_mem_27 (T52 elt) S14 elt (List (Prod S14 elt)) Bool (R_mem5 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect5 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
               (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
               a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
               a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
               () -> () -> Bool -> (R_mem5 a1) -> a2 -> a2) -> (T52 a1) ->
               Bool -> (R_mem5 a1) -> a2
r_mem_rect5 k f f0 f1 f2 _ _ r =
  case r of {
   R_mem_24 s -> f s __;
   R_mem_25 s k' _x l -> f0 s k' _x l __ __ __;
   R_mem_26 s k' _x l -> f1 s k' _x l __ __ __;
   R_mem_27 s k' _x l _res r0 ->
    f2 s k' _x l __ __ __ _res r0 (r_mem_rect5 k f f0 f1 f2 l _res r0)}

r_mem_rec5 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
              (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
              a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
              a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
              () -> () -> Bool -> (R_mem5 a1) -> a2 -> a2) -> (T52 a1) ->
              Bool -> (R_mem5 a1) -> a2
r_mem_rec5 =
  r_mem_rect5

mem_rect2 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
             (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 a1) ->
             S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () -> a2) ->
             ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> ()
             -> a2 -> a2) -> (T52 a1) -> a2
mem_rect2 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> False;
      Cons p l ->
       case p of {
        Pair k' _ ->
         case compare29 k k' of {
          LT -> False;
          EQ -> True;
          GT -> mem15 k l}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = mem_rect2 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare29 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (mem15 k s)

mem_rec2 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 -> (List
            (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 a1) -> S14 -> a1
            -> (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
            a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () -> a2
            -> a2) -> (T52 a1) -> a2
mem_rec2 =
  mem_rect2

r_mem_correct2 :: Key9 -> (T52 a1) -> Bool -> R_mem5 a1
r_mem_correct2 k s _res =
  unsafeCoerce mem_rect2 k (\y _ z _ -> eq_rect_r False (R_mem_24 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r False (R_mem_25 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r True (R_mem_26 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (mem15 k y2) (R_mem_27 y y0 y1 y2 (mem15 k y2)
      (y6 (mem15 k y2) __)) z) s _res __

find9 :: Key9 -> (T52 a1) -> Option a1
find9 k s =
  case s of {
   Nil -> None;
   Cons p s' ->
    case p of {
     Pair k' x ->
      case compare29 k k' of {
       LT -> None;
       EQ -> Some x;
       GT -> find9 k s'}}}

data R_find5 elt =
   R_find_24 (T52 elt)
 | R_find_25 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_find_26 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_find_27 (T52 elt) S14 elt (List (Prod S14 elt)) (Option elt) (R_find5
                                                                  elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect5 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
                (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
                a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
                a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> ()
                -> () -> () -> (Option a1) -> (R_find5 a1) -> a2 -> a2) ->
                (T52 a1) -> (Option a1) -> (R_find5 a1) -> a2
r_find_rect5 k f f0 f1 f2 _ _ r =
  case r of {
   R_find_24 s -> f s __;
   R_find_25 s k' x s' -> f0 s k' x s' __ __ __;
   R_find_26 s k' x s' -> f1 s k' x s' __ __ __;
   R_find_27 s k' x s' _res r0 ->
    f2 s k' x s' __ __ __ _res r0 (r_find_rect5 k f f0 f1 f2 s' _res r0)}

r_find_rec5 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
               (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
               a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
               a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
               () -> () -> (Option a1) -> (R_find5 a1) -> a2 -> a2) -> (T52
               a1) -> (Option a1) -> (R_find5 a1) -> a2
r_find_rec5 =
  r_find_rect5

find_rect2 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
              (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
              a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
              a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
              () -> () -> a2 -> a2) -> (T52 a1) -> a2
find_rect2 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> None;
      Cons p s' ->
       case p of {
        Pair k' x ->
         case compare29 k k' of {
          LT -> None;
          EQ -> Some x;
          GT -> find9 k s'}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = find_rect2 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare29 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (find9 k s)

find_rec2 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
             (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 a1) ->
             S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () -> a2) ->
             ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> ()
             -> a2 -> a2) -> (T52 a1) -> a2
find_rec2 =
  find_rect2

r_find_correct2 :: Key9 -> (T52 a1) -> (Option a1) -> R_find5 a1
r_find_correct2 k s _res =
  unsafeCoerce find_rect2 k (\y _ z _ -> eq_rect_r None (R_find_24 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r None (R_find_25 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r (Some y1) (R_find_26 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (find9 k y2) (R_find_27 y y0 y1 y2 (find9 k y2)
      (y6 (find9 k y2) __)) z) s _res __

add18 :: Key9 -> a1 -> (T52 a1) -> T52 a1
add18 k x s =
  case s of {
   Nil -> Cons (Pair k x) Nil;
   Cons p l ->
    case p of {
     Pair k' y ->
      case compare29 k k' of {
       LT -> Cons (Pair k x) s;
       EQ -> Cons (Pair k x) l;
       GT -> Cons (Pair k' y) (add18 k x l)}}}

data R_add5 elt =
   R_add_24 (T52 elt)
 | R_add_25 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_add_26 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_add_27 (T52 elt) S14 elt (List (Prod S14 elt)) (T52 elt) (R_add5 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect5 :: Key9 -> a1 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1
               -> (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
               a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
               a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
               () -> () -> (T52 a1) -> (R_add5 a1) -> a2 -> a2) -> (T52 
               a1) -> (T52 a1) -> (R_add5 a1) -> a2
r_add_rect5 k x f f0 f1 f2 _ _ r =
  case r of {
   R_add_24 s -> f s __;
   R_add_25 s k' y l -> f0 s k' y l __ __ __;
   R_add_26 s k' y l -> f1 s k' y l __ __ __;
   R_add_27 s k' y l _res r0 ->
    f2 s k' y l __ __ __ _res r0 (r_add_rect5 k x f f0 f1 f2 l _res r0)}

r_add_rec5 :: Key9 -> a1 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1
              -> (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
              a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
              a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
              () -> () -> (T52 a1) -> (R_add5 a1) -> a2 -> a2) -> (T52 
              a1) -> (T52 a1) -> (R_add5 a1) -> a2
r_add_rec5 =
  r_add_rect5

add_rect2 :: Key9 -> a1 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1
             -> (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
             a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
             a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
             () -> () -> a2 -> a2) -> (T52 a1) -> a2
add_rect2 k x f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Cons (Pair k x) Nil;
      Cons p l ->
       case p of {
        Pair k' y ->
         case compare29 k k' of {
          LT -> Cons (Pair k x) s;
          EQ -> Cons (Pair k x) l;
          GT -> Cons (Pair k' y) (add18 k x l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = add_rect2 k x f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare29 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (add18 k x s)

add_rec2 :: Key9 -> a1 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
            (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 a1) -> S14
            -> a1 -> (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52
            a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () -> a2
            -> a2) -> (T52 a1) -> a2
add_rec2 =
  add_rect2

r_add_correct2 :: Key9 -> a1 -> (T52 a1) -> (T52 a1) -> R_add5 a1
r_add_correct2 k x s _res =
  add_rect2 k x (\y _ z _ -> eq_rect_r (Cons (Pair k x) Nil) (R_add_24 y) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y) (R_add_25 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ ->
    eq_rect_r (Cons (Pair k x) y2) (R_add_26 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (add18 k x y2)) (R_add_27 y y0 y1 y2
      (add18 k x y2) (y6 (add18 k x y2) __)) z) s _res __

remove15 :: Key9 -> (T52 a1) -> T52 a1
remove15 k s =
  case s of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k' x ->
      case compare29 k k' of {
       LT -> s;
       EQ -> l;
       GT -> Cons (Pair k' x) (remove15 k l)}}}

data R_remove5 elt =
   R_remove_24 (T52 elt)
 | R_remove_25 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_remove_26 (T52 elt) S14 elt (List (Prod S14 elt))
 | R_remove_27 (T52 elt) S14 elt (List (Prod S14 elt)) (T52 elt) (R_remove5
                                                                 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect5 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
                  (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
                  a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> ()
                  -> a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) ->
                  () -> () -> () -> (T52 a1) -> (R_remove5 a1) -> a2 -> a2)
                  -> (T52 a1) -> (T52 a1) -> (R_remove5 a1) -> a2
r_remove_rect5 k f f0 f1 f2 _ _ r =
  case r of {
   R_remove_24 s -> f s __;
   R_remove_25 s k' x l -> f0 s k' x l __ __ __;
   R_remove_26 s k' x l -> f1 s k' x l __ __ __;
   R_remove_27 s k' x l _res r0 ->
    f2 s k' x l __ __ __ _res r0 (r_remove_rect5 k f f0 f1 f2 l _res r0)}

r_remove_rec5 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
                 (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
                 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> ()
                 -> a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) ->
                 () -> () -> () -> (T52 a1) -> (R_remove5 a1) -> a2 -> a2) ->
                 (T52 a1) -> (T52 a1) -> (R_remove5 a1) -> a2
r_remove_rec5 =
  r_remove_rect5

remove_rect2 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
                (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
                a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
                a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> ()
                -> () -> () -> a2 -> a2) -> (T52 a1) -> a2
remove_rect2 k f2 f1 f0 f s =
  eq_rect_r
    (case s of {
      Nil -> Nil;
      Cons p l ->
       case p of {
        Pair k' x ->
         case compare29 k k' of {
          LT -> s;
          EQ -> l;
          GT -> Cons (Pair k' x) (remove15 k l)}}})
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      Nil -> f3 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = remove_rect2 k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare29 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}}) (remove15 k s)

remove_rec2 :: Key9 -> ((T52 a1) -> () -> a2) -> ((T52 a1) -> S14 -> a1 ->
               (List (Prod S14 a1)) -> () -> () -> () -> a2) -> ((T52 
               a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
               a2) -> ((T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
               () -> () -> a2 -> a2) -> (T52 a1) -> a2
remove_rec2 =
  remove_rect2

r_remove_correct2 :: Key9 -> (T52 a1) -> (T52 a1) -> R_remove5 a1
r_remove_correct2 k s _res =
  unsafeCoerce remove_rect2 k (\y _ z _ -> eq_rect_r Nil (R_remove_24 y) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y (R_remove_25 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ z _ -> eq_rect_r y2 (R_remove_26 y y0 y1 y2) z)
    (\y y0 y1 y2 _ _ _ y6 z _ ->
    eq_rect_r (Cons (Pair y0 y1) (remove15 k y2)) (R_remove_27 y y0 y1 y2
      (remove15 k y2) (y6 (remove15 k y2) __)) z) s _res __

elements15 :: (T52 a1) -> T52 a1
elements15 m =
  m

fold15 :: (Key9 -> a1 -> a2 -> a2) -> (T52 a1) -> a2 -> a2
fold15 f m acc =
  case m of {
   Nil -> acc;
   Cons p m' -> case p of {
                 Pair k e -> fold15 f m' (f k e acc)}}

data R_fold2 elt a =
   R_fold_6 (T52 elt) a
 | R_fold_7 (T52 elt) a S14 elt (List (Prod S14 elt)) a (R_fold2 elt a)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_fold_rect2 :: (Key9 -> a1 -> a2 -> a2) -> ((T52 a1) -> a2 -> () -> a3) ->
                ((T52 a1) -> a2 -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
                a2 -> (R_fold2 a1 a2) -> a3 -> a3) -> (T52 a1) -> a2 -> a2 ->
                (R_fold2 a1 a2) -> a3
r_fold_rect2 f f0 f1 _ _ _ r =
  case r of {
   R_fold_6 m acc -> f0 m acc __;
   R_fold_7 m acc k e m' _res r0 ->
    f1 m acc k e m' __ _res r0 (r_fold_rect2 f f0 f1 m' (f k e acc) _res r0)}

r_fold_rec2 :: (Key9 -> a1 -> a2 -> a2) -> ((T52 a1) -> a2 -> () -> a3) ->
               ((T52 a1) -> a2 -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
               a2 -> (R_fold2 a1 a2) -> a3 -> a3) -> (T52 a1) -> a2 -> a2 ->
               (R_fold2 a1 a2) -> a3
r_fold_rec2 =
  r_fold_rect2

fold_rect2 :: (Key9 -> a1 -> a2 -> a2) -> ((T52 a1) -> a2 -> () -> a3) ->
              ((T52 a1) -> a2 -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
              a3 -> a3) -> (T52 a1) -> a2 -> a3
fold_rect2 f1 f0 f m acc =
  eq_rect_r
    (case m of {
      Nil -> acc;
      Cons p m' -> case p of {
                    Pair k e -> fold15 f1 m' (f1 k e acc)}})
    (let {f2 = f0 m acc} in
     let {f3 = f m acc} in
     case m of {
      Nil -> f2 __;
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f4 = f3 t0 e l __} in
         let {hrec = fold_rect2 f1 f0 f l (f1 t0 e acc)} in f4 hrec}})
    (fold15 f1 m acc)

fold_rec2 :: (Key9 -> a1 -> a2 -> a2) -> ((T52 a1) -> a2 -> () -> a3) ->
             ((T52 a1) -> a2 -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> a3
             -> a3) -> (T52 a1) -> a2 -> a3
fold_rec2 =
  fold_rect2

r_fold_correct2 :: (Key9 -> a1 -> a2 -> a2) -> (T52 a1) -> a2 -> a2 ->
                   R_fold2 a1 a2
r_fold_correct2 f m acc _res =
  fold_rect2 f (\y y0 _ z _ -> eq_rect_r y0 (R_fold_6 y y0) z)
    (\y y0 y1 y2 y3 _ y5 z _ ->
    eq_rect_r (fold15 f y3 (f y1 y2 y0)) (R_fold_7 y y0 y1 y2 y3
      (fold15 f y3 (f y1 y2 y0)) (y5 (fold15 f y3 (f y1 y2 y0)) __)) z) m acc
    _res __

equal15 :: (a1 -> a1 -> Bool) -> (T52 a1) -> (T52 a1) -> Bool
equal15 cmp m m' =
  case m of {
   Nil -> case m' of {
           Nil -> True;
           Cons _ _ -> False};
   Cons p l ->
    case p of {
     Pair x e ->
      case m' of {
       Nil -> False;
       Cons p0 l' ->
        case p0 of {
         Pair x' e' ->
          case compare29 x x' of {
           EQ -> andb (cmp e e') (equal15 cmp l l');
           _ -> False}}}}}

data R_equal2 elt =
   R_equal_12 (T52 elt) (T52 elt)
 | R_equal_13 (T52 elt) (T52 elt) S14 elt (List (Prod S14 elt)) S14 elt 
 (List (Prod S14 elt)) Bool (R_equal2 elt)
 | R_equal_14 (T52 elt) (T52 elt) S14 elt (List (Prod S14 elt)) S14 elt 
 (List (Prod S14 elt)) (Compare S14)
 | R_equal_15 (T52 elt) (T52 elt) (T52 elt) (T52 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_equal_rect2 :: (a1 -> a1 -> Bool) -> ((T52 a1) -> (T52 a1) -> () -> () ->
                 a2) -> ((T52 a1) -> (T52 a1) -> S14 -> a1 -> (List
                 (Prod S14 a1)) -> () -> S14 -> a1 -> (List (Prod S14 a1)) ->
                 () -> () -> () -> Bool -> (R_equal2 a1) -> a2 -> a2) ->
                 ((T52 a1) -> (T52 a1) -> S14 -> a1 -> (List (Prod S14 a1))
                 -> () -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> (Compare
                 S14) -> () -> () -> a2) -> ((T52 a1) -> (T52 a1) -> (T52 
                 a1) -> () -> (T52 a1) -> () -> () -> a2) -> (T52 a1) -> (T52
                 a1) -> Bool -> (R_equal2 a1) -> a2
r_equal_rect2 cmp f f0 f1 f2 _ _ _ r =
  case r of {
   R_equal_12 m m' -> f m m' __ __;
   R_equal_13 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (r_equal_rect2 cmp f f0 f1 f2 l l' _res r0);
   R_equal_14 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   R_equal_15 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

r_equal_rec2 :: (a1 -> a1 -> Bool) -> ((T52 a1) -> (T52 a1) -> () -> () ->
                a2) -> ((T52 a1) -> (T52 a1) -> S14 -> a1 -> (List
                (Prod S14 a1)) -> () -> S14 -> a1 -> (List (Prod S14 a1)) ->
                () -> () -> () -> Bool -> (R_equal2 a1) -> a2 -> a2) -> ((T52
                a1) -> (T52 a1) -> S14 -> a1 -> (List (Prod S14 a1)) -> () ->
                S14 -> a1 -> (List (Prod S14 a1)) -> () -> (Compare S14) ->
                () -> () -> a2) -> ((T52 a1) -> (T52 a1) -> (T52 a1) -> () ->
                (T52 a1) -> () -> () -> a2) -> (T52 a1) -> (T52 a1) -> Bool
                -> (R_equal2 a1) -> a2
r_equal_rec2 =
  r_equal_rect2

equal_rect2 :: (a1 -> a1 -> Bool) -> ((T52 a1) -> (T52 a1) -> () -> () -> a2)
               -> ((T52 a1) -> (T52 a1) -> S14 -> a1 -> (List (Prod S14 a1))
               -> () -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> ()
               -> a2 -> a2) -> ((T52 a1) -> (T52 a1) -> S14 -> a1 -> (List
               (Prod S14 a1)) -> () -> S14 -> a1 -> (List (Prod S14 a1)) ->
               () -> (Compare S14) -> () -> () -> a2) -> ((T52 a1) -> (T52
               a1) -> (T52 a1) -> () -> (T52 a1) -> () -> () -> a2) -> (T52
               a1) -> (T52 a1) -> a2
equal_rect2 cmp f2 f1 f0 f m m' =
  eq_rect_r
    (case m of {
      Nil -> case m' of {
              Nil -> True;
              Cons _ _ -> False};
      Cons p l ->
       case p of {
        Pair x e ->
         case m' of {
          Nil -> False;
          Cons p0 l' ->
           case p0 of {
            Pair x' e' ->
             case compare29 x x' of {
              EQ -> andb (cmp e e') (equal15 cmp l l');
              _ -> False}}}}})
    (let {f3 = f2 m m'} in
     let {f4 = f1 m m'} in
     let {f5 = f0 m m'} in
     let {f6 = f m m'} in
     let {f7 = f6 m __} in
     let {f8 = f7 m' __} in
     case m of {
      Nil ->
       let {f9 = f3 __} in case m' of {
                            Nil -> f9 __;
                            Cons _ _ -> f8 __};
      Cons p l ->
       case p of {
        Pair t0 e ->
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case m' of {
          Nil -> f8 __;
          Cons p0 l0 ->
           case p0 of {
            Pair t1 e0 ->
             let {f11 = f9 t1 e0 l0 __} in
             let {f12 = let {_x = compare29 t0 t1} in f11 _x __} in
             let {f13 = f10 t1 e0 l0 __} in
             let {
              f14 = \_ _ ->
               let {hrec = equal_rect2 cmp f2 f1 f0 f l l0} in f13 __ __ hrec}
             in
             case compare29 t0 t1 of {
              EQ -> f14 __ __;
              _ -> f12 __}}}}}) (equal15 cmp m m')

equal_rec2 :: (a1 -> a1 -> Bool) -> ((T52 a1) -> (T52 a1) -> () -> () -> a2)
              -> ((T52 a1) -> (T52 a1) -> S14 -> a1 -> (List (Prod S14 a1))
              -> () -> S14 -> a1 -> (List (Prod S14 a1)) -> () -> () -> () ->
              a2 -> a2) -> ((T52 a1) -> (T52 a1) -> S14 -> a1 -> (List
              (Prod S14 a1)) -> () -> S14 -> a1 -> (List (Prod S14 a1)) -> ()
              -> (Compare S14) -> () -> () -> a2) -> ((T52 a1) -> (T52 
              a1) -> (T52 a1) -> () -> (T52 a1) -> () -> () -> a2) -> (T52
              a1) -> (T52 a1) -> a2
equal_rec2 =
  equal_rect2

r_equal_correct2 :: (a1 -> a1 -> Bool) -> (T52 a1) -> (T52 a1) -> Bool ->
                    R_equal2 a1
r_equal_correct2 cmp m m' _res =
  equal_rect2 cmp (\y y0 _ _ z _ -> eq_rect_r True (R_equal_12 y y0) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ ->
    eq_rect_r (andb (cmp y2 y6) (equal15 cmp y3 y7)) (R_equal_13 y y0 y1 y2
      y3 y5 y6 y7 (equal15 cmp y3 y7) (y11 (equal15 cmp y3 y7) __)) z)
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ ->
    eq_rect_r False (R_equal_14 y y0 y1 y2 y3 y5 y6 y7 y9) z)
    (\y y0 y1 _ y3 _ _ z _ -> eq_rect_r False (R_equal_15 y y0 y1 y3) z) m m'
    _res __

map20 :: (a1 -> a2) -> (T52 a1) -> T52 a2
map20 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f e)) (map20 f m')}}

mapi9 :: (Key9 -> a1 -> a2) -> (T52 a1) -> T52 a2
mapi9 f m =
  case m of {
   Nil -> Nil;
   Cons p m' -> case p of {
                 Pair k e -> Cons (Pair k (f k e)) (mapi9 f m')}}

option_cons2 :: Key9 -> (Option a1) -> (List (Prod Key9 a1)) -> List
                (Prod Key9 a1)
option_cons2 k o l =
  case o of {
   Some e -> Cons (Pair k e) l;
   None -> l}

map2_l2 :: ((Option a1) -> (Option a2) -> Option a3) -> (T52 a1) -> T52 a3
map2_l2 f m =
  case m of {
   Nil -> Nil;
   Cons p l ->
    case p of {
     Pair k e -> option_cons2 k (f (Some e) None) (map2_l2 f l)}}

map2_r2 :: ((Option a1) -> (Option a2) -> Option a3) -> (T52 a2) -> T52 a3
map2_r2 f m' =
  case m' of {
   Nil -> Nil;
   Cons p l' ->
    case p of {
     Pair k e' -> option_cons2 k (f None (Some e')) (map2_r2 f l')}}

map21 :: ((Option a1) -> (Option a2) -> Option a3) -> (T52 a1) -> (T52 
         a2) -> T52 a3
map21 f m =
  case m of {
   Nil -> map2_r2 f;
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       map2_aux m' =
         case m' of {
          Nil -> map2_l2 f m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare29 k k' of {
              LT -> option_cons2 k (f (Some e) None) (map21 f l m');
              EQ -> option_cons2 k (f (Some e) (Some e')) (map21 f l l');
              GT -> option_cons2 k' (f None (Some e')) (map2_aux l')}}}}
      in map2_aux}}

combine2 :: (T52 a1) -> (T52 a2) -> T52 (Prod (Option a1) (Option a2))
combine2 m =
  case m of {
   Nil -> map20 (\e' -> Pair None (Some e'));
   Cons p l ->
    case p of {
     Pair k e ->
      let {
       combine_aux m' =
         case m' of {
          Nil -> map20 (\e0 -> Pair (Some e0) None) m;
          Cons p0 l' ->
           case p0 of {
            Pair k' e' ->
             case compare29 k k' of {
              LT -> Cons (Pair k (Pair (Some e) None)) (combine2 l m');
              EQ -> Cons (Pair k (Pair (Some e) (Some e'))) (combine2 l l');
              GT -> Cons (Pair k' (Pair None (Some e'))) (combine_aux l')}}}}
      in combine_aux}}

fold_right_pair2 :: (a1 -> a2 -> a3 -> a3) -> (List (Prod a1 a2)) -> a3 -> a3
fold_right_pair2 f l i =
  fold_right (\p -> f (fst p) (snd p)) i l

map2_alt2 :: ((Option a1) -> (Option a2) -> Option a3) -> (T52 a1) -> (T52
             a2) -> List (Prod Key9 a3)
map2_alt2 f m m' =
  let {m0 = combine2 m m'} in
  let {m1 = map20 (\p -> f (fst p) (snd p)) m0} in
  fold_right_pair2 option_cons2 m1 Nil

at_least_one2 :: (Option a1) -> (Option a2) -> Option
                 (Prod (Option a1) (Option a2))
at_least_one2 o o' =
  case o of {
   Some _ -> Some (Pair o o');
   None -> case o' of {
            Some _ -> Some (Pair o o');
            None -> None}}

at_least_one_then_f2 :: ((Option a1) -> (Option a2) -> Option a3) -> (Option
                        a1) -> (Option a2) -> Option a3
at_least_one_then_f2 f o o' =
  case o of {
   Some _ -> f o o';
   None -> case o' of {
            Some _ -> f o o';
            None -> None}}

data R_mem6 elt =
   R_mem_28 (Tree4 elt)
 | R_mem_29 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T Bool (R_mem6 elt)
 | R_mem_30 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T
 | R_mem_31 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T Bool (R_mem6 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_mem_rect6 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
               a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () -> Bool
               -> (R_mem6 a1) -> a2 -> a2) -> ((Tree4 a1) -> (Tree4 a1) ->
               Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () -> a2) ->
               ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T ->
               () -> () -> () -> Bool -> (R_mem6 a1) -> a2 -> a2) -> (Tree4
               a1) -> Bool -> (R_mem6 a1) -> a2
r_mem_rect6 x f f0 f1 f2 _ _ r =
  case r of {
   R_mem_28 m -> f m __;
   R_mem_29 m l y _x r0 _x0 _res r1 ->
    f0 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect6 x f f0 f1 f2 l _res r1);
   R_mem_30 m l y _x r0 _x0 -> f1 m l y _x r0 _x0 __ __ __;
   R_mem_31 m l y _x r0 _x0 _res r1 ->
    f2 m l y _x r0 _x0 __ __ __ _res r1 (r_mem_rect6 x f f0 f1 f2 r0 _res r1)}

r_mem_rec6 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
              a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () -> Bool
              -> (R_mem6 a1) -> a2 -> a2) -> ((Tree4 a1) -> (Tree4 a1) ->
              Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T ->
              () -> () -> () -> Bool -> (R_mem6 a1) -> a2 -> a2) -> (Tree4
              a1) -> Bool -> (R_mem6 a1) -> a2
r_mem_rec6 =
  r_mem_rect6

data R_find6 elt =
   R_find_28 (Tree4 elt)
 | R_find_29 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Option elt) 
 (R_find6 elt)
 | R_find_30 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T
 | R_find_31 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Option elt) 
 (R_find6 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_find_rect6 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
                a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
                (Option a1) -> (R_find6 a1) -> a2 -> a2) -> ((Tree4 a1) ->
                (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> ()
                -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4
                a1) -> T -> () -> () -> () -> (Option a1) -> (R_find6 
                a1) -> a2 -> a2) -> (Tree4 a1) -> (Option a1) -> (R_find6 
                a1) -> a2
r_find_rect6 x f f0 f1 f2 _ _ r =
  case r of {
   R_find_28 m -> f m __;
   R_find_29 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_find_rect6 x f f0 f1 f2 l _res r1);
   R_find_30 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_find_31 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_find_rect6 x f f0 f1 f2 r0 _res r1)}

r_find_rec6 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
               a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
               (Option a1) -> (R_find6 a1) -> a2 -> a2) -> ((Tree4 a1) ->
               (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4
               a1) -> T -> () -> () -> () -> (Option a1) -> (R_find6 
               a1) -> a2 -> a2) -> (Tree4 a1) -> (Option a1) -> (R_find6 
               a1) -> a2
r_find_rec6 =
  r_find_rect6

data R_bal4 elt =
   R_bal_45 (Tree4 elt) Key8 elt (Tree4 elt)
 | R_bal_46 (Tree4 elt) Key8 elt (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T
 | R_bal_47 (Tree4 elt) Key8 elt (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T
 | R_bal_48 (Tree4 elt) Key8 elt (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T (Tree4 elt) Key8 elt (Tree4 elt) T
 | R_bal_49 (Tree4 elt) Key8 elt (Tree4 elt)
 | R_bal_50 (Tree4 elt) Key8 elt (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T
 | R_bal_51 (Tree4 elt) Key8 elt (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T
 | R_bal_52 (Tree4 elt) Key8 elt (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T (Tree4 elt) Key8 elt (Tree4 elt) T
 | R_bal_53 (Tree4 elt) Key8 elt (Tree4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_bal_rect2 :: ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> () -> () ->
               a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> () ->
               (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> ()
               -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () ->
               () -> () -> a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 
               a1) -> () -> () -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 
               a1) -> T -> () -> () -> () -> (Tree4 a1) -> Key8 -> a1 ->
               (Tree4 a1) -> T -> () -> a2) -> ((Tree4 a1) -> Key8 -> a1 ->
               (Tree4 a1) -> () -> () -> () -> () -> () -> a2) -> ((Tree4 
               a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> () -> () -> () ->
               (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> ()
               -> () -> () -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T ->
               () -> () -> () -> () -> a2) -> ((Tree4 a1) -> Key8 -> a1 ->
               (Tree4 a1) -> () -> () -> () -> () -> (Tree4 a1) -> Key8 -> a1
               -> (Tree4 a1) -> T -> () -> () -> () -> (Tree4 a1) -> Key8 ->
               a1 -> (Tree4 a1) -> T -> () -> a2) -> ((Tree4 a1) -> Key8 ->
               a1 -> (Tree4 a1) -> () -> () -> () -> () -> a2) -> (Tree4 
               a1) -> Key8 -> a1 -> (Tree4 a1) -> (Tree4 a1) -> (R_bal4 
               a1) -> a2
r_bal_rect2 f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ r =
  case r of {
   R_bal_45 x x0 x1 x2 -> f x x0 x1 x2 __ __ __;
   R_bal_46 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_47 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_48 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_49 x x0 x1 x2 -> f3 x x0 x1 x2 __ __ __ __ __;
   R_bal_50 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __;
   R_bal_51 x x0 x1 x2 x3 x4 x5 x6 x7 ->
    f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __;
   R_bal_52 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __;
   R_bal_53 x x0 x1 x2 -> f7 x x0 x1 x2 __ __ __ __}

r_bal_rec2 :: ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> () -> () ->
              a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> () ->
              (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> ()
              -> a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> ()
              -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () ->
              () -> () -> a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 
              a1) -> () -> () -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T
              -> () -> () -> () -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 
              a1) -> T -> () -> a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4
              a1) -> () -> () -> () -> () -> () -> a2) -> ((Tree4 a1) -> Key8
              -> a1 -> (Tree4 a1) -> () -> () -> () -> () -> (Tree4 a1) ->
              Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () -> a2) ->
              ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> () -> () -> ()
              -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () ->
              () -> () -> a2) -> ((Tree4 a1) -> Key8 -> a1 -> (Tree4 
              a1) -> () -> () -> () -> () -> (Tree4 a1) -> Key8 -> a1 ->
              (Tree4 a1) -> T -> () -> () -> () -> (Tree4 a1) -> Key8 -> a1
              -> (Tree4 a1) -> T -> () -> a2) -> ((Tree4 a1) -> Key8 -> a1 ->
              (Tree4 a1) -> () -> () -> () -> () -> a2) -> (Tree4 a1) -> Key8
              -> a1 -> (Tree4 a1) -> (Tree4 a1) -> (R_bal4 a1) -> a2
r_bal_rec2 =
  r_bal_rect2

data R_add6 elt =
   R_add_28 (Tree4 elt)
 | R_add_29 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Tree4 elt) 
 (R_add6 elt)
 | R_add_30 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T
 | R_add_31 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Tree4 elt) 
 (R_add6 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_add_rect6 :: Key8 -> a1 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) ->
               (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> ()
               -> (Tree4 a1) -> (R_add6 a1) -> a2 -> a2) -> ((Tree4 a1) ->
               (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> ()
               -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4
               a1) -> T -> () -> () -> () -> (Tree4 a1) -> (R_add6 a1) -> a2
               -> a2) -> (Tree4 a1) -> (Tree4 a1) -> (R_add6 a1) -> a2
r_add_rect6 x d f f0 f1 f2 _ _ r =
  case r of {
   R_add_28 m -> f m __;
   R_add_29 m l y d' r0 h _res r1 ->
    f0 m l y d' r0 h __ __ __ _res r1 (r_add_rect6 x d f f0 f1 f2 l _res r1);
   R_add_30 m l y d' r0 h -> f1 m l y d' r0 h __ __ __;
   R_add_31 m l y d' r0 h _res r1 ->
    f2 m l y d' r0 h __ __ __ _res r1 (r_add_rect6 x d f f0 f1 f2 r0 _res r1)}

r_add_rec6 :: Key8 -> a1 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4
              a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
              (Tree4 a1) -> (R_add6 a1) -> a2 -> a2) -> ((Tree4 a1) -> (Tree4
              a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () -> a2)
              -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T
              -> () -> () -> () -> (Tree4 a1) -> (R_add6 a1) -> a2 -> a2) ->
              (Tree4 a1) -> (Tree4 a1) -> (R_add6 a1) -> a2
r_add_rec6 =
  r_add_rect6

data R_remove_min4 elt =
   R_remove_min_10 (Tree4 elt) Key8 elt (Tree4 elt)
 | R_remove_min_11 (Tree4 elt) Key8 elt (Tree4 elt) (Tree4 elt) Key8 
 elt (Tree4 elt) T (Prod (Tree4 elt) (Prod Key8 elt)) (R_remove_min4 elt) 
 (Tree4 elt) (Prod Key8 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_min_rect2 :: ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> a2) ->
                      ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> (Tree4 
                      a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Prod
                      (Tree4 a1) (Prod Key8 a1)) -> (R_remove_min4 a1) -> a2
                      -> (Tree4 a1) -> (Prod Key8 a1) -> () -> a2) -> (Tree4
                      a1) -> Key8 -> a1 -> (Tree4 a1) -> (Prod (Tree4 a1)
                      (Prod Key8 a1)) -> (R_remove_min4 a1) -> a2
r_remove_min_rect2 f f0 _ _ _ _ _ r =
  case r of {
   R_remove_min_10 l x d r0 -> f l x d r0 __;
   R_remove_min_11 l x d r0 ll lx ld lr _x _res r1 l' m ->
    f0 l x d r0 ll lx ld lr _x __ _res r1
      (r_remove_min_rect2 f f0 ll lx ld lr _res r1) l' m __}

r_remove_min_rec2 :: ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> () -> a2) ->
                     ((Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> (Tree4 
                     a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Prod
                     (Tree4 a1) (Prod Key8 a1)) -> (R_remove_min4 a1) -> a2
                     -> (Tree4 a1) -> (Prod Key8 a1) -> () -> a2) -> (Tree4
                     a1) -> Key8 -> a1 -> (Tree4 a1) -> (Prod (Tree4 a1)
                     (Prod Key8 a1)) -> (R_remove_min4 a1) -> a2
r_remove_min_rec2 =
  r_remove_min_rect2

data R_merge4 elt =
   R_merge_15 (Tree4 elt) (Tree4 elt)
 | R_merge_16 (Tree4 elt) (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T
 | R_merge_17 (Tree4 elt) (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T (Tree4 elt) Key8 elt (Tree4 elt) T (Tree4 elt) (Prod Key8 elt) Key8 
 elt
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_merge_rect2 :: ((Tree4 a1) -> (Tree4 a1) -> () -> a2) -> ((Tree4 a1) ->
                 (Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T ->
                 () -> () -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> (Tree4 
                 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                 a1) -> (Prod Key8 a1) -> () -> Key8 -> a1 -> () -> a2) ->
                 (Tree4 a1) -> (Tree4 a1) -> (Tree4 a1) -> (R_merge4 
                 a1) -> a2
r_merge_rect2 f f0 f1 _ _ _ r =
  case r of {
   R_merge_15 x x0 -> f x x0 __;
   R_merge_16 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_merge_17 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __}

r_merge_rec2 :: ((Tree4 a1) -> (Tree4 a1) -> () -> a2) -> ((Tree4 a1) ->
                (Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T ->
                () -> () -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> (Tree4 
                a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                a1) -> (Prod Key8 a1) -> () -> Key8 -> a1 -> () -> a2) ->
                (Tree4 a1) -> (Tree4 a1) -> (Tree4 a1) -> (R_merge4 a1) -> a2
r_merge_rec2 =
  r_merge_rect2

data R_remove6 elt =
   R_remove_28 (Tree4 elt)
 | R_remove_29 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Tree4 elt) 
 (R_remove6 elt)
 | R_remove_30 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T
 | R_remove_31 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Tree4 elt) 
 (R_remove6 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_remove_rect6 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4
                  a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
                  (Tree4 a1) -> (R_remove6 a1) -> a2 -> a2) -> ((Tree4 
                  a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () ->
                  () -> () -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1
                  -> (Tree4 a1) -> T -> () -> () -> () -> (Tree4 a1) ->
                  (R_remove6 a1) -> a2 -> a2) -> (Tree4 a1) -> (Tree4 
                  a1) -> (R_remove6 a1) -> a2
r_remove_rect6 x f f0 f1 f2 _ _ r =
  case r of {
   R_remove_28 m -> f m __;
   R_remove_29 m l y d r0 _x _res r1 ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_remove_rect6 x f f0 f1 f2 l _res r1);
   R_remove_30 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_remove_31 m l y d r0 _x _res r1 ->
    f2 m l y d r0 _x __ __ __ _res r1
      (r_remove_rect6 x f f0 f1 f2 r0 _res r1)}

r_remove_rec6 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
                 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
                 (Tree4 a1) -> (R_remove6 a1) -> a2 -> a2) -> ((Tree4 
                 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () ->
                 () -> () -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1
                 -> (Tree4 a1) -> T -> () -> () -> () -> (Tree4 a1) ->
                 (R_remove6 a1) -> a2 -> a2) -> (Tree4 a1) -> (Tree4 
                 a1) -> (R_remove6 a1) -> a2
r_remove_rec6 =
  r_remove_rect6

data R_concat4 elt =
   R_concat_15 (Tree4 elt) (Tree4 elt)
 | R_concat_16 (Tree4 elt) (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T
 | R_concat_17 (Tree4 elt) (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) 
 T (Tree4 elt) Key8 elt (Tree4 elt) T (Tree4 elt) (Prod Key8 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_concat_rect2 :: ((Tree4 a1) -> (Tree4 a1) -> () -> a2) -> ((Tree4 a1) ->
                  (Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T
                  -> () -> () -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> (Tree4
                  a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                  a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                  a1) -> (Prod Key8 a1) -> () -> a2) -> (Tree4 a1) -> (Tree4
                  a1) -> (Tree4 a1) -> (R_concat4 a1) -> a2
r_concat_rect2 f f0 f1 _ _ _ r =
  case r of {
   R_concat_15 x x0 -> f x x0 __;
   R_concat_16 x x0 x1 x2 x3 x4 x5 -> f0 x x0 x1 x2 x3 x4 x5 __ __;
   R_concat_17 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
    f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __}

r_concat_rec2 :: ((Tree4 a1) -> (Tree4 a1) -> () -> a2) -> ((Tree4 a1) ->
                 (Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T ->
                 () -> () -> a2) -> ((Tree4 a1) -> (Tree4 a1) -> (Tree4 
                 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                 a1) -> (Prod Key8 a1) -> () -> a2) -> (Tree4 a1) -> (Tree4
                 a1) -> (Tree4 a1) -> (R_concat4 a1) -> a2
r_concat_rec2 =
  r_concat_rect2

data R_split2 elt =
   R_split_12 (Tree4 elt)
 | R_split_13 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Triple4 elt) 
 (R_split2 elt) (Tree4 elt) (Option elt) (Tree4 elt)
 | R_split_14 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T
 | R_split_15 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Triple4 elt) 
 (R_split2 elt) (Tree4 elt) (Option elt) (Tree4 elt)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_split_rect2 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
                 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
                 (Triple4 a1) -> (R_split2 a1) -> a2 -> (Tree4 a1) -> (Option
                 a1) -> (Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
                 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
                 a2) -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 
                 a1) -> T -> () -> () -> () -> (Triple4 a1) -> (R_split2 
                 a1) -> a2 -> (Tree4 a1) -> (Option a1) -> (Tree4 a1) -> ()
                 -> a2) -> (Tree4 a1) -> (Triple4 a1) -> (R_split2 a1) -> a2
r_split_rect2 x f f0 f1 f2 _ _ r =
  case r of {
   R_split_12 m -> f m __;
   R_split_13 m l y d r0 _x _res r1 ll o rl ->
    f0 m l y d r0 _x __ __ __ _res r1 (r_split_rect2 x f f0 f1 f2 l _res r1)
      ll o rl __;
   R_split_14 m l y d r0 _x -> f1 m l y d r0 _x __ __ __;
   R_split_15 m l y d r0 _x _res r1 rl o rr ->
    f2 m l y d r0 _x __ __ __ _res r1 (r_split_rect2 x f f0 f1 f2 r0 _res r1)
      rl o rr __}

r_split_rec2 :: S14 -> ((Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
                a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () ->
                (Triple4 a1) -> (R_split2 a1) -> a2 -> (Tree4 a1) -> (Option
                a1) -> (Tree4 a1) -> () -> a2) -> ((Tree4 a1) -> (Tree4 
                a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> () -> () -> a2)
                -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 
                a1) -> T -> () -> () -> () -> (Triple4 a1) -> (R_split2 
                a1) -> a2 -> (Tree4 a1) -> (Option a1) -> (Tree4 a1) -> () ->
                a2) -> (Tree4 a1) -> (Triple4 a1) -> (R_split2 a1) -> a2
r_split_rec2 =
  r_split_rect2

data R_map_option2 elt x =
   R_map_option_9 (Tree4 elt)
 | R_map_option_10 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T x (Tree4 x) 
 (R_map_option2 elt x) (Tree4 x) (R_map_option2 elt x)
 | R_map_option_11 (Tree4 elt) (Tree4 elt) Key8 elt (Tree4 elt) T (Tree4 x) 
 (R_map_option2 elt x) (Tree4 x) (R_map_option2 elt x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map_option_rect2 :: (Key8 -> a1 -> Option a2) -> ((Tree4 a1) -> () -> a3)
                      -> ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4
                      a1) -> T -> () -> a2 -> () -> (Tree4 a2) ->
                      (R_map_option2 a1 a2) -> a3 -> (Tree4 a2) ->
                      (R_map_option2 a1 a2) -> a3 -> a3) -> ((Tree4 a1) ->
                      (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> ()
                      -> (Tree4 a2) -> (R_map_option2 a1 a2) -> a3 -> (Tree4
                      a2) -> (R_map_option2 a1 a2) -> a3 -> a3) -> (Tree4 
                      a1) -> (Tree4 a2) -> (R_map_option2 a1 a2) -> a3
r_map_option_rect2 f f0 f1 f2 _ _ r =
  case r of {
   R_map_option_9 m -> f0 m __;
   R_map_option_10 m l x d r0 _x d' _res0 r1 _res r2 ->
    f1 m l x d r0 _x __ d' __ _res0 r1
      (r_map_option_rect2 f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect2 f f0 f1 f2 r0 _res r2);
   R_map_option_11 m l x d r0 _x _res0 r1 _res r2 ->
    f2 m l x d r0 _x __ __ _res0 r1
      (r_map_option_rect2 f f0 f1 f2 l _res0 r1) _res r2
      (r_map_option_rect2 f f0 f1 f2 r0 _res r2)}

r_map_option_rec2 :: (Key8 -> a1 -> Option a2) -> ((Tree4 a1) -> () -> a3) ->
                     ((Tree4 a1) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 
                     a1) -> T -> () -> a2 -> () -> (Tree4 a2) ->
                     (R_map_option2 a1 a2) -> a3 -> (Tree4 a2) ->
                     (R_map_option2 a1 a2) -> a3 -> a3) -> ((Tree4 a1) ->
                     (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> ()
                     -> (Tree4 a2) -> (R_map_option2 a1 a2) -> a3 -> (Tree4
                     a2) -> (R_map_option2 a1 a2) -> a3 -> a3) -> (Tree4 
                     a1) -> (Tree4 a2) -> (R_map_option2 a1 a2) -> a3
r_map_option_rec2 =
  r_map_option_rect2

data R_map2_opt2 elt x0 x =
   R_map2_opt_12 (Tree4 elt) (Tree4 x0)
 | R_map2_opt_13 (Tree4 elt) (Tree4 x0) (Tree4 elt) Key8 elt (Tree4 elt) 
 T
 | R_map2_opt_14 (Tree4 elt) (Tree4 x0) (Tree4 elt) Key8 elt (Tree4 elt) 
 T (Tree4 x0) Key8 x0 (Tree4 x0) T (Tree4 x0) (Option x0) (Tree4 x0) 
 x (Tree4 x) (R_map2_opt2 elt x0 x) (Tree4 x) (R_map2_opt2 elt x0 x)
 | R_map2_opt_15 (Tree4 elt) (Tree4 x0) (Tree4 elt) Key8 elt (Tree4 elt) 
 T (Tree4 x0) Key8 x0 (Tree4 x0) T (Tree4 x0) (Option x0) (Tree4 x0) 
 (Tree4 x) (R_map2_opt2 elt x0 x) (Tree4 x) (R_map2_opt2 elt x0 x)
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

r_map2_opt_rect2 :: (Key8 -> a1 -> (Option a2) -> Option a3) -> ((Tree4 
                    a1) -> Tree4 a3) -> ((Tree4 a2) -> Tree4 a3) -> ((Tree4
                    a1) -> (Tree4 a2) -> () -> a4) -> ((Tree4 a1) -> (Tree4
                    a2) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> ()
                    -> () -> a4) -> ((Tree4 a1) -> (Tree4 a2) -> (Tree4 
                    a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                    a2) -> Key8 -> a2 -> (Tree4 a2) -> T -> () -> (Tree4 
                    a2) -> (Option a2) -> (Tree4 a2) -> () -> a3 -> () ->
                    (Tree4 a3) -> (R_map2_opt2 a1 a2 a3) -> a4 -> (Tree4 
                    a3) -> (R_map2_opt2 a1 a2 a3) -> a4 -> a4) -> ((Tree4 
                    a1) -> (Tree4 a2) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4
                    a1) -> T -> () -> (Tree4 a2) -> Key8 -> a2 -> (Tree4 
                    a2) -> T -> () -> (Tree4 a2) -> (Option a2) -> (Tree4 
                    a2) -> () -> () -> (Tree4 a3) -> (R_map2_opt2 a1 
                    a2 a3) -> a4 -> (Tree4 a3) -> (R_map2_opt2 a1 a2 
                    a3) -> a4 -> a4) -> (Tree4 a1) -> (Tree4 a2) -> (Tree4
                    a3) -> (R_map2_opt2 a1 a2 a3) -> a4
r_map2_opt_rect2 f mapl mapr f0 f1 f2 f3 _ _ _ r =
  case r of {
   R_map2_opt_12 m1 m2 -> f0 m1 m2 __;
   R_map2_opt_13 m1 m2 l1 x1 d1 r1 _x -> f1 m1 m2 l1 x1 d1 r1 _x __ __;
   R_map2_opt_14 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' e _res0
    r0 _res r2 ->
    f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
      _res0 r0 (r_map2_opt_rect2 f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
      _res r2 (r_map2_opt_rect2 f mapl mapr f0 f1 f2 f3 r1 r2' _res r2);
   R_map2_opt_15 m1 m2 l1 x1 d1 r1 _x _x0 _x1 _x2 _x3 _x4 l2' o2 r2' _res0 r0
    _res r2 ->
    f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
      r0 (r_map2_opt_rect2 f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
      (r_map2_opt_rect2 f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)}

r_map2_opt_rec2 :: (Key8 -> a1 -> (Option a2) -> Option a3) -> ((Tree4 
                   a1) -> Tree4 a3) -> ((Tree4 a2) -> Tree4 a3) -> ((Tree4
                   a1) -> (Tree4 a2) -> () -> a4) -> ((Tree4 a1) -> (Tree4
                   a2) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> ()
                   -> () -> a4) -> ((Tree4 a1) -> (Tree4 a2) -> (Tree4 
                   a1) -> Key8 -> a1 -> (Tree4 a1) -> T -> () -> (Tree4 
                   a2) -> Key8 -> a2 -> (Tree4 a2) -> T -> () -> (Tree4 
                   a2) -> (Option a2) -> (Tree4 a2) -> () -> a3 -> () ->
                   (Tree4 a3) -> (R_map2_opt2 a1 a2 a3) -> a4 -> (Tree4 
                   a3) -> (R_map2_opt2 a1 a2 a3) -> a4 -> a4) -> ((Tree4 
                   a1) -> (Tree4 a2) -> (Tree4 a1) -> Key8 -> a1 -> (Tree4
                   a1) -> T -> () -> (Tree4 a2) -> Key8 -> a2 -> (Tree4 
                   a2) -> T -> () -> (Tree4 a2) -> (Option a2) -> (Tree4 
                   a2) -> () -> () -> (Tree4 a3) -> (R_map2_opt2 a1 a2 
                   a3) -> a4 -> (Tree4 a3) -> (R_map2_opt2 a1 a2 a3) -> a4 ->
                   a4) -> (Tree4 a1) -> (Tree4 a2) -> (Tree4 a3) ->
                   (R_map2_opt2 a1 a2 a3) -> a4
r_map2_opt_rec2 =
  r_map2_opt_rect2

fold'2 :: (Key8 -> a1 -> a2 -> a2) -> (Tree4 a1) -> a2 -> a2
fold'2 f s =
  fold15 f (elements14 s)

flatten_e4 :: (Enumeration4 a1) -> List (Prod Key8 a1)
flatten_e4 e =
  case e of {
   End4 -> Nil;
   More4 x e0 t r -> Cons (Pair x e0) (app (elements14 t) (flatten_e4 r))}

type Bst2 elt = Tree4 elt
  -- singleton inductive, whose constructor was Bst
  
this4 :: (Bst2 a1) -> Tree4 a1
this4 b =
  b

type T53 elt = Bst2 elt

type Key10 = S14

empty16 :: T53 a1
empty16 =
  empty14

is_empty16 :: (T53 a1) -> Bool
is_empty16 m =
  is_empty14 (this4 m)

add19 :: Key10 -> a1 -> (T53 a1) -> T53 a1
add19 x e m =
  add17 x e (this4 m)

remove16 :: Key10 -> (T53 a1) -> T53 a1
remove16 x m =
  remove14 x (this4 m)

mem16 :: Key10 -> (T53 a1) -> Bool
mem16 x m =
  mem14 x (this4 m)

find10 :: Key10 -> (T53 a1) -> Option a1
find10 x m =
  find8 x (this4 m)

map22 :: (a1 -> a2) -> (T53 a1) -> T53 a2
map22 f m =
  map18 f (this4 m)

mapi10 :: (Key10 -> a1 -> a2) -> (T53 a1) -> T53 a2
mapi10 f m =
  mapi8 f (this4 m)

map23 :: ((Option a1) -> (Option a2) -> Option a3) -> (T53 a1) -> (T53 
         a2) -> T53 a3
map23 f m m' =
  map19 f (this4 m) (this4 m')

elements16 :: (T53 a1) -> List (Prod Key10 a1)
elements16 m =
  elements14 (this4 m)

cardinal12 :: (T53 a1) -> Nat
cardinal12 m =
  cardinal11 (this4 m)

fold16 :: (Key10 -> a1 -> a2 -> a2) -> (T53 a1) -> a2 -> a2
fold16 f m i =
  fold14 f (this4 m) i

equal16 :: (a1 -> a1 -> Bool) -> (T53 a1) -> (T53 a1) -> Bool
equal16 cmp m m' =
  equal14 cmp (this4 m) (this4 m')

emptySCHMap :: T53 ConcreteChoice
emptySCHMap =
  empty16

type SCH_MAP_TYPE = T53 ConcreteChoice

data StateT =
   State SC_MAP_TYPE SCH_MAP_TYPE
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

sc :: StateT -> SC_MAP_TYPE
sc s =
  case s of {
   State sc0 _ -> sc0}

sch :: StateT -> SCH_MAP_TYPE
sch s =
  case s of {
   State _ sch0 -> sch0}

emptyState :: StateT
emptyState =
  State emptySCMap emptySCHMap

data Money =
   AvailableMoney IdentCCT
 | AddMoney Money Money
 | ConstMoney Cash
 | MoneyFromChoice IdentChoiceT Person Money
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

evalMoney :: StateT -> Money -> Cash
evalMoney sta mon =
  case mon of {
   AvailableMoney i ->
    case find7 i (sc sta) of {
     Some c0 ->
      case c0 of {
       Pair _ c1 -> case c1 of {
                     NotRedeemed c _ -> c;
                     _ -> 0}};
     None -> 0};
   AddMoney mon1 mon2 ->
    (Prelude.+) (evalMoney sta mon1) (evalMoney sta mon2);
   ConstMoney c -> c;
   MoneyFromChoice i p mon0 ->
    case find10 (Pair i p) (sch sta) of {
     Some c -> c;
     None -> evalMoney sta mon0}}

data Observation =
   BelowTimeout Timeout
 | AndObs Observation Observation
 | OrObs Observation Observation
 | NotObs Observation
 | PersonChoseThis IdentChoiceT Person ConcreteChoice
 | PersonChoseSomething IdentChoiceT Person
 | ValueGE Money Money
 | TrueObs
 | FalseObs
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

expired :: Timeout -> Timeout -> Bool
expired e ee =
  leb ee e

interpretObs :: StateT -> Observation -> OST -> Bool
interpretObs sta obs os =
  case obs of {
   BelowTimeout n -> negb (expired (blockNumber os) n);
   AndObs obs1 obs2 ->
    andb (interpretObs sta obs1 os) (interpretObs sta obs2 os);
   OrObs obs1 obs2 ->
    orb (interpretObs sta obs1 os) (interpretObs sta obs2 os);
   NotObs obs0 -> negb (interpretObs sta obs0 os);
   PersonChoseThis choice_id person reference_choice ->
    case find10 (Pair choice_id person) (sch sta) of {
     Some actual_choice -> eqb0 actual_choice reference_choice;
     None -> False};
   PersonChoseSomething choice_id person ->
    mem16 (Pair choice_id person) (sch sta);
   ValueGE a b -> geb (evalMoney sta a) (evalMoney sta b);
   TrueObs -> True;
   FalseObs -> False}

data Contract =
   Null
 | CommitCash IdentCCT Person Money Timeout Timeout Contract Contract
 | RedeemCC IdentCCT Contract
 | Pay IdentPayT Person Person Money Timeout Contract
 | Both Contract Contract
 | Choice Observation Contract Contract
 | When Observation Timeout Contract Contract
  deriving (Prelude.Show, Prelude.Ord, Prelude.Read, Prelude.Eq)

contract_rect :: a1 -> (IdentCCT -> Person -> Money -> Timeout -> Timeout ->
                 Contract -> a1 -> Contract -> a1 -> a1) -> (IdentCCT ->
                 Contract -> a1 -> a1) -> (IdentPayT -> Person -> Person ->
                 Money -> Timeout -> Contract -> a1 -> a1) -> (Contract -> a1
                 -> Contract -> a1 -> a1) -> (Observation -> Contract -> a1
                 -> Contract -> a1 -> a1) -> (Observation -> Timeout ->
                 Contract -> a1 -> Contract -> a1 -> a1) -> Contract -> a1
contract_rect f f0 f1 f2 f3 f4 f5 c =
  case c of {
   Null -> f;
   CommitCash i p m t t0 c0 c1 ->
    f0 i p m t t0 c0 (contract_rect f f0 f1 f2 f3 f4 f5 c0) c1
      (contract_rect f f0 f1 f2 f3 f4 f5 c1);
   RedeemCC i c0 -> f1 i c0 (contract_rect f f0 f1 f2 f3 f4 f5 c0);
   Pay i p p0 m t c0 ->
    f2 i p p0 m t c0 (contract_rect f f0 f1 f2 f3 f4 f5 c0);
   Both c0 c1 ->
    f3 c0 (contract_rect f f0 f1 f2 f3 f4 f5 c0) c1
      (contract_rect f f0 f1 f2 f3 f4 f5 c1);
   Choice o c0 c1 ->
    f4 o c0 (contract_rect f f0 f1 f2 f3 f4 f5 c0) c1
      (contract_rect f f0 f1 f2 f3 f4 f5 c1);
   When o t c0 c1 ->
    f5 o t c0 (contract_rect f f0 f1 f2 f3 f4 f5 c0) c1
      (contract_rect f f0 f1 f2 f3 f4 f5 c1)}

merge5 :: (List (Prod IdentCCT CCStatus)) -> (List (Prod IdentCCT CCStatus))
          -> List (Prod IdentCCT CCStatus)
merge5 l1 l2 =
  let {
   merge_aux l3 =
     case l1 of {
      Nil -> l3;
      Cons a1 l1' ->
       case l3 of {
        Nil -> l1;
        Cons a2 l2' ->
         case case a1 of {
               Pair ia1 ba1 ->
                case a2 of {
                 Pair ib2 bb2 ->
                  case ba1 of {
                   Pair _ ca1 ->
                    case bb2 of {
                     Pair _ cb2 ->
                      case ca1 of {
                       NotRedeemed _ ea1 ->
                        case cb2 of {
                         NotRedeemed _ eb2 ->
                          case ltb ea1 eb2 of {
                           True -> True;
                           False ->
                            case gtb ea1 eb2 of {
                             True -> False;
                             False -> leb ia1 ib2}};
                         _ -> True};
                       ExpiredAndRedeemed ->
                        case cb2 of {
                         ExpiredAndRedeemed -> True;
                         _ -> False};
                       ManuallyRedeemed ->
                        case cb2 of {
                         NotRedeemed _ _ -> False;
                         _ -> True}}}}}} of {
          True -> Cons a1 (merge5 l1' l3);
          False -> Cons a2 (merge_aux l2')}}}}
  in merge_aux l2

merge_list_to_stack :: (List (Option (List (Prod IdentCCT CCStatus)))) ->
                       (List (Prod IdentCCT CCStatus)) -> List
                       (Option (List (Prod IdentCCT CCStatus)))
merge_list_to_stack stack l =
  case stack of {
   Nil -> Cons (Some l) Nil;
   Cons y stack' ->
    case y of {
     Some l' -> Cons None (merge_list_to_stack stack' (merge5 l' l));
     None -> Cons (Some l) stack'}}

merge_stack :: (List (Option (List (Prod IdentCCT CCStatus)))) -> List
               (Prod IdentCCT CCStatus)
merge_stack stack =
  case stack of {
   Nil -> Nil;
   Cons y stack' ->
    case y of {
     Some l -> merge5 l (merge_stack stack');
     None -> merge_stack stack'}}

iter_merge :: (List (Option (List (Prod IdentCCT CCStatus)))) -> (List
              (Prod IdentCCT CCStatus)) -> List (Prod IdentCCT CCStatus)
iter_merge stack l =
  case l of {
   Nil -> merge_stack stack;
   Cons a l' -> iter_merge (merge_list_to_stack stack (Cons a Nil)) l'}

sort :: (List (Prod IdentCCT CCStatus)) -> List (Prod IdentCCT CCStatus)
sort =
  iter_merge Nil

flatten_stack :: (List (Option (List (Prod IdentCCT CCStatus)))) -> List
                 (Prod IdentCCT CCStatus)
flatten_stack stack =
  case stack of {
   Nil -> Nil;
   Cons o stack' ->
    case o of {
     Some l -> app l (flatten_stack stack');
     None -> flatten_stack stack'}}

sortByExpirationDate :: (List (Prod IdentCCT CCStatus)) -> List
                        (Prod IdentCCT CCStatus)
sortByExpirationDate =
  sort

discountFromPairList :: Cash -> (List (Prod IdentCCT CCStatus)) -> Option
                        (List (Prod IdentCCT CCStatus))
discountFromPairList v l =
  case l of {
   Nil -> case eq_dec0 v 0 of {
           Left -> Some Nil;
           Right -> None};
   Cons p0 t ->
    case p0 of {
     Pair ident c ->
      case c of {
       Pair p c0 ->
        case c0 of {
         NotRedeemed ve e ->
          case z_le_gt_dec v ve of {
           Left -> Some (Cons (Pair ident (Pair p (NotRedeemed
            ((Prelude.-) ve v) e))) Nil);
           Right ->
            case discountFromPairList ((Prelude.-) v ve) t of {
             Some dt -> Some (Cons (Pair ident (Pair p (NotRedeemed 0 e)))
              dt);
             None -> None}};
         _ -> Some t}}}}

discountFromValid :: (CCStatus -> Bool) -> Cash -> SC_MAP_TYPE -> Option
                     SC_MAP_TYPE
discountFromValid f v m =
  case discountFromPairList v
         (sortByExpirationDate
           (filter (\k_va -> case k_va of {
                              Pair _ va -> f va}) (elements13 m))) of {
   Some changes_to_map -> Some
    (fold_left (\mi el -> case el of {
                           Pair k va -> add16 k va mi}) changes_to_map m);
   None -> None}

isRedeemable :: Person -> Timeout -> CCStatus -> Bool
isRedeemable p e ccs =
  case ccs of {
   Pair ep css ->
    case css of {
     NotRedeemed _ ee -> andb (eqb0 ep p) (negb (expired e ee));
     _ -> False}}

updateMap :: SC_MAP_TYPE -> Person -> Timeout -> Cash -> Option SC_MAP_TYPE
updateMap mx p e v =
  discountFromValid (isRedeemable p e) v mx

stateUpdate :: StateT -> Person -> Person -> Timeout -> Cash -> Option StateT
stateUpdate st9 from _ bn val =
  case st9 of {
   State sc0 sch0 ->
    case updateMap sc0 from bn val of {
     Some newccs -> Some (State newccs sch0);
     None -> None}}

nulldec :: Contract -> Sumbool
nulldec con =
  case con of {
   Null -> Left;
   _ -> Right}


stepWrap :: InputT -> StateT -> Contract -> OST -> (StateT, Contract, [Action])
stepWrap inp sta c os = (nsta, ncon, toNormalList nac)
  where Pair (Pair nsta ncon) nac = step inp sta c os

step :: InputT -> StateT -> Contract -> OST -> Prod (Prod StateT Contract) AS
step inp st9 c os =
  let {bn = blockNumber os} in
  case c of {
   Null -> Pair (Pair st9 Null) Nil;
   CommitCash ident person val start_timeout end_timeout con1 con2 ->
    let {cexs = expired bn end_timeout} in
    let {cexe = expired bn start_timeout} in
    let {ccs = sc st9} in
    let {cval = evalMoney st9 val} in
    let {
     cns = Pair person
      (case orb cexs cexe of {
        True -> ManuallyRedeemed;
        False -> NotRedeemed cval end_timeout})}
    in
    let {ust = add16 ident cns ccs} in
    let {nst = State ust (sch st9)} in
    case orb cexe cexs of {
     True -> Pair (Pair nst con2) Nil;
     False ->
      case mem1 (CC ident person cval end_timeout) (cc inp) of {
       True -> Pair (Pair nst con1) (Cons (SuccessfulCommit ident person
        (evalMoney st9 val) end_timeout) Nil);
       False -> Pair (Pair st9 (CommitCash ident person val start_timeout
        end_timeout con1 con2)) Nil}};
   RedeemCC ident con ->
    case find7 ident (sc st9) of {
     Some c0 ->
      case c0 of {
       Pair person c1 ->
        case c1 of {
         NotRedeemed val ee ->
          case expired bn ee of {
           True -> Pair (Pair st9 con) Nil;
           False ->
            case mem4 (RC ident person val) (rc inp) of {
             True -> Pair (Pair (State
              (add16 ident (Pair person ManuallyRedeemed) (sc st9))
              (sch st9)) con) (Cons (CommitRedeemed ident person val) Nil);
             False -> Pair (Pair st9 (RedeemCC ident con)) Nil}};
         ExpiredAndRedeemed -> Pair (Pair st9 con) Nil;
         ManuallyRedeemed -> Pair (Pair st9 con) (Cons (DuplicateRedeem ident
          person) Nil)}};
     None -> Pair (Pair st9 (RedeemCC ident con)) Nil};
   Pay idpay from to val expi con ->
    let {cval = evalMoney st9 val} in
    case expired (blockNumber os) expi of {
     True -> Pair (Pair st9 con) (Cons (ExpiredPay idpay from to cval) Nil);
     False ->
      case case find1 (Pair idpay to) (rp inp) of {
            Some claimed_val -> eqb0 claimed_val cval;
            None -> False} of {
       True ->
        case geb cval 0 of {
         True ->
          case stateUpdate st9 from to bn cval of {
           Some newstate -> Pair (Pair newstate con) (Cons (SuccessfulPay
            idpay from to cval) Nil);
           None -> Pair (Pair st9 con) (Cons (FailedPay idpay from to cval)
            Nil)};
         False -> Pair (Pair st9 con) (Cons (FailedPay idpay from to cval)
          Nil)};
       False -> Pair (Pair st9 (Pay idpay from to val expi con)) Nil}};
   Both con1 con2 ->
    case step inp st9 con1 os of {
     Pair res1 ac1 ->
      case res1 of {
       Pair st10 ncon1 ->
        case step inp st10 con2 os of {
         Pair res2 ac2 ->
          case res2 of {
           Pair st11 ncon2 -> Pair (Pair st11
            (case nulldec ncon1 of {
              Left -> ncon2;
              Right ->
               case nulldec ncon2 of {
                Left -> ncon1;
                Right -> Both ncon1 ncon2}})) (app ac1 ac2)}}}};
   Choice obs conT conF ->
    case interpretObs st9 obs os of {
     True -> Pair (Pair st9 conT) Nil;
     False -> Pair (Pair st9 conF) Nil};
   When obs expi con con2 ->
    case expired (blockNumber os) expi of {
     True -> Pair (Pair st9 con2) Nil;
     False ->
      case interpretObs st9 obs os of {
       True -> Pair (Pair st9 con) Nil;
       False -> Pair (Pair st9 (When obs expi con con2)) Nil}}}

sc_kv_eqb :: (Prod Key7 CCStatus) -> (Prod Key7 CCStatus) -> Bool
sc_kv_eqb a b =
  case a of {
   Pair k1 c1 ->
    case b of {
     Pair k2 c2 ->
      andb (case eq_dec37 k1 k2 of {
             Left -> True;
             Right -> False})
        (case c1 of {
          Pair p c ->
           case c2 of {
            Pair p0 c0 ->
             case c of {
              NotRedeemed c3 t ->
               case c0 of {
                NotRedeemed c4 t0 ->
                 andb (andb (eqb0 p p0) (eqb0 c3 c4)) (eqb0 t t0);
                _ -> False};
              ExpiredAndRedeemed ->
               case c0 of {
                ExpiredAndRedeemed -> eqb0 p p0;
                _ -> False};
              ManuallyRedeemed ->
               case c0 of {
                ManuallyRedeemed -> eqb0 p p0;
                _ -> False}}}})}}

sch_kv_eqb :: (Prod Key10 ConcreteChoice) -> (Prod Key10 ConcreteChoice) ->
              Bool
sch_kv_eqb a b =
  case a of {
   Pair k c ->
    case b of {
     Pair k0 c0 ->
      andb (case eq_dec43 k k0 of {
             Left -> True;
             Right -> False}) (eqb0 c c0)}}

list_eqb :: (a1 -> a2 -> Bool) -> (List a1) -> (List a2) -> Bool
list_eqb f x y =
  case x of {
   Nil -> case y of {
           Nil -> True;
           Cons _ _ -> False};
   Cons a0 x0 ->
    case y of {
     Nil -> False;
     Cons b0 y0 -> andb (f a0 b0) (list_eqb f x0 y0)}}

stateT_eqb :: StateT -> StateT -> Bool
stateT_eqb a b =
  andb (list_eqb sc_kv_eqb (elements13 (sc a)) (elements13 (sc b)))
    (list_eqb sch_kv_eqb (elements16 (sch a)) (elements16 (sch b)))

step_order :: Contract -> Contract -> InputT -> StateT -> StateT -> OST -> AS
              -> AS -> Sumbool
step_order c nc inp st9 nst os ac nac =
  contract_rect (\nc0 _ st10 nst0 _ _ nac0 _ ->
    eq_rec_r st10 (\_ ->
      eq_rec_r Null (\_ ->
        eq_rec_r Nil (eq_rec_r True Right (stateT_eqb st10 st10)) nac0) nc0)
      nst0 __ __) (\i p m t t0 c1 _ c2 _ nc0 inp0 st10 nst0 os0 _ nac0 _ ->
    let {
     b = orb (expired (blockNumber os0) t) (expired (blockNumber os0) t0)}
    in
    case b of {
     True ->
      eq_rec_r (State
        (add16 i (Pair p
          (case orb (expired (blockNumber os0) t0)
                  (expired (blockNumber os0) t) of {
            True -> ManuallyRedeemed;
            False -> NotRedeemed (evalMoney st10 m) t0})) (sc st10))
        (sch st10)) (\_ ->
        eq_rec_r c2 (\_ -> eq_rec_r Nil (eq_rec nc0 Left c2) nac0) nc0) nst0
        __ __;
     False ->
      let {b0 = mem1 (CC i p (evalMoney st10 m) t0) (cc inp0)} in
      case b0 of {
       True ->
        eq_rec_r (State
          (add16 i (Pair p
            (case orb (expired (blockNumber os0) t0)
                    (expired (blockNumber os0) t) of {
              True -> ManuallyRedeemed;
              False -> NotRedeemed (evalMoney st10 m) t0})) (sc st10))
          (sch st10)) (\_ ->
          eq_rec_r c1 (\_ ->
            eq_rec_r (Cons (SuccessfulCommit i p (evalMoney st10 m) t0) Nil)
              (eq_rec nc0 Left c1) nac0) nc0) nst0 __ __;
       False ->
        eq_rec_r st10 (\_ ->
          eq_rec_r (CommitCash i p m t t0 c1 c2) (\_ ->
            eq_rec_r Nil Right nac0) nc0) nst0 __ __}})
    (\i c0 _ nc0 inp0 st10 nst0 os0 _ nac0 _ ->
    let {o = find7 i (sc st10)} in
    case o of {
     Some c1 ->
      case c1 of {
       Pair p c2 ->
        case c2 of {
         NotRedeemed c3 t ->
          let {b = mem4 (RC i p c3) (rc inp0)} in
          case b of {
           True ->
            let {b0 = expired (blockNumber os0) t} in
            case b0 of {
             True ->
              eq_rec_r st10 (\_ ->
                eq_rec_r c0 (\_ ->
                  eq_rec_r Nil (eq_rec nst0 (eq_rec nc0 Left c0) st10) nac0)
                  nc0) nst0 __ __;
             False ->
              eq_rec_r (State (add16 i (Pair p ManuallyRedeemed) (sc st10))
                (sch st10)) (\_ ->
                eq_rec_r c0 (\_ ->
                  eq_rec_r (Cons (CommitRedeemed i p c3) Nil)
                    (eq_rec nst0 (eq_rec nc0 Left c0) (State
                      (add16 i (Pair p ManuallyRedeemed) (sc st10))
                      (sch st10))) nac0) nc0) nst0 __ __};
           False ->
            let {b0 = expired (blockNumber os0) t} in
            case b0 of {
             True ->
              eq_rec_r st10 (\_ ->
                eq_rec_r c0 (\_ -> eq_rec_r Nil Left nac0) nc0) nst0 __ __;
             False ->
              eq_rec_r st10 (\_ ->
                eq_rec_r (RedeemCC i c0) (\_ -> eq_rec_r Nil Right nac0) nc0)
                nst0 __ __}};
         ExpiredAndRedeemed ->
          eq_rec_r st10 (\_ ->
            eq_rec_r c0 (\_ -> eq_rec_r Nil Left nac0) nc0) nst0 __ __;
         ManuallyRedeemed ->
          eq_rec_r st10 (\_ ->
            eq_rec_r c0 (\_ ->
              eq_rec_r (Cons (DuplicateRedeem i p) Nil) Left nac0) nc0) nst0
            __ __}};
     None ->
      eq_rec_r st10 (\_ ->
        eq_rec_r (RedeemCC i c0) (\_ -> eq_rec_r Nil Right nac0) nc0) nst0 __
        __}) (\i p p0 m t c0 _ nc0 inp0 st10 nst0 os0 _ nac0 _ ->
    let {b = expired (blockNumber os0) t} in
    case b of {
     True -> Left;
     False ->
      let {
       b0 = case find1 (Pair i p0) (rp inp0) of {
             Some claimed_val -> eqb0 claimed_val (evalMoney st10 m);
             None -> False}}
      in
      case b0 of {
       True ->
        let {o = stateUpdate st10 p p0 (blockNumber os0) (evalMoney st10 m)}
        in
        case o of {
         Some s ->
          let {b1 = geb (evalMoney st10 m) 0} in
          case b1 of {
           True ->
            eq_rec_r s (\_ ->
              eq_rec_r c0 (\_ ->
                eq_rec_r (Cons (SuccessfulPay i p p0 (evalMoney st10 m)) Nil)
                  Left nac0) nc0) nst0 __ __;
           False -> Left};
         None ->
          let {b1 = geb (evalMoney st10 m) 0} in
          case b1 of {
           True ->
            eq_rec_r st10 (\_ ->
              eq_rec_r c0 (\_ ->
                eq_rec_r (Cons (FailedPay i p p0 (evalMoney st10 m)) Nil)
                  Left nac0) nc0) nst0 __ __;
           False -> Left}};
       False ->
        eq_rec_r st10 (\_ ->
          eq_rec_r (Pay i p p0 m t c0) (\_ -> eq_rec_r Nil Right nac0) nc0)
          nst0 __ __}})
    (\c1 iHc1 c2 iHc2 nc0 inp0 st10 nst0 os0 ac0 nac0 _ ->
    let {x = \nst1 nc1 ac1 nac1 -> iHc1 nc1 inp0 st10 nst1 os0 ac1 nac1 __}
    in
    let {p = step inp0 st10 c1 os0} in
    case p of {
     Pair p0 a ->
      case p0 of {
       Pair s c0 ->
        let {h0 = \ac1 -> x s c0 ac1 a} in
        let {x0 = \nc1 nst1 ac1 nac1 -> iHc2 nc1 inp0 s nst1 os0 ac1 nac1 __}
        in
        let {p1 = step inp0 s c2 os0} in
        case p1 of {
         Pair p2 a0 ->
          case p2 of {
           Pair s0 c3 ->
            let {h1 = \ac1 -> x0 c3 s0 ac1 a0} in
            let {s1 = nulldec c0} in
            case s1 of {
             Left ->
              eq_rec_r s0 (\_ ->
                eq_rec_r c3 (\_ ->
                  eq_rec_r (app a a0)
                    (eq_rec_r Null (\h2 ->
                      eq_rec_r s0 (\_ ->
                        eq_rec_r c3 (\_ ->
                          eq_rec_r (app a a0) (\_ ->
                            let {s2 = h2 Nil} in
                            case s2 of {
                             Left ->
                              let {s3 = h1 a} in
                              case s3 of {
                               Left -> Left;
                               Right ->
                                eq_rec_r c3
                                  (prod_rec (\_ _ ->
                                    let {h5 = h2 ac0} in
                                    sumbool_rec (\_ ->
                                      let {h3 = h1 ac0} in
                                      sumbool_rec (\_ -> Left) (\_ -> Left)
                                        h3) (\_ ->
                                      let {h3 = h1 ac0} in
                                      sumbool_rec (\_ -> Left) (\_ -> Left)
                                        h3) h5) p2) c2};
                             Right ->
                              eq_rec_r Null
                                (let {s3 = h1 a} in
                                 case s3 of {
                                  Left ->
                                   prod_rec (\_ _ ->
                                     let {h5 = h2 ac0} in
                                     sumbool_rec (\_ ->
                                       let {h3 = h1 ac0} in
                                       sumbool_rec (\_ -> Left) (\_ -> Left)
                                         h3) (\_ ->
                                       let {h3 = h1 ac0} in
                                       sumbool_rec (\_ -> Left) (\_ -> Left)
                                         h3) h5) p2;
                                  Right -> eq_rec_r c3 Left c2}) c1}) nac0 __)
                          nc0 __) nst0 __) c0 h0) nac0) nc0) nst0 __ __;
             Right ->
              let {s2 = nulldec c3} in
              case s2 of {
               Left ->
                eq_rec_r s0 (\_ ->
                  eq_rec_r c0 (\_ ->
                    eq_rec_r (app a a0)
                      (eq_rec_r Null (\h2 ->
                        eq_rec_r s0 (\_ ->
                          eq_rec_r c0 (\_ ->
                            eq_rec_r (app a a0) (\_ ->
                              let {s3 = h0 Nil} in
                              case s3 of {
                               Left ->
                                let {s4 = h2 a} in
                                case s4 of {
                                 Left -> Left;
                                 Right ->
                                  eq_rec_r Null
                                    (prod_rec (\_ _ ->
                                      let {h5 = h0 ac0} in
                                      sumbool_rec (\_ ->
                                        let {h3 = h2 ac0} in
                                        sumbool_rec (\_ -> Left) (\_ -> Left)
                                          h3) (\_ ->
                                        let {h3 = h2 ac0} in
                                        sumbool_rec (\_ -> Left) (\_ -> Left)
                                          h3) h5) p2) c2};
                               Right ->
                                eq_rec_r c0
                                  (let {s4 = h2 a} in
                                   case s4 of {
                                    Left ->
                                     prod_rec (\_ _ ->
                                       let {h5 = h0 ac0} in
                                       sumbool_rec (\_ ->
                                         let {h3 = h2 ac0} in
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Left) h3) (\_ ->
                                         let {h3 = h2 ac0} in
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Left) h3) h5) p2;
                                    Right -> eq_rec_r Null Left c2}) c1})
                              nac0 __) nc0 __) nst0 __) c3 h1) nac0) nc0)
                  nst0 __ __;
               Right ->
                eq_rec_r s0 (\_ ->
                  eq_rec_r (Both c0 c3) (\_ ->
                    eq_rec_r (app a a0)
                      (eq_rec_r s0 (\_ ->
                        eq_rec_r (Both c0 c3) (\_ ->
                          eq_rec_r (app a a0) (\_ ->
                            let {s3 = h0 Nil} in
                            case s3 of {
                             Left ->
                              let {s4 = h1 a} in
                              case s4 of {
                               Left -> Left;
                               Right ->
                                eq_rec_r c3
                                  (prod_rec (\_ _ ->
                                    let {h5 = h0 ac0} in
                                    sumbool_rec (\_ ->
                                      let {h2 = h1 ac0} in
                                      sumbool_rec (\_ -> Left) (\_ -> Left)
                                        h2) (\_ ->
                                      let {h2 = h1 ac0} in
                                      sumbool_rec (\_ -> Left) (\_ -> Left)
                                        h2) h5) p2) c2};
                             Right ->
                              eq_rec_r c0
                                (let {s4 = h1 a} in
                                 case s4 of {
                                  Left ->
                                   prod_rec (\_ _ ->
                                     let {h5 = h0 ac0} in
                                     sumbool_rec (\_ ->
                                       let {h2 = h1 ac0} in
                                       sumbool_rec (\_ -> Left) (\_ -> Left)
                                         h2) (\_ ->
                                       let {h2 = h1 ac0} in
                                       sumbool_rec (\_ -> Left) (\_ -> Left)
                                         h2) h5) p2;
                                  Right -> eq_rec_r c3 Right c2}) c1}) nac0
                            __) nc0 __) nst0 __) nac0) nc0) nst0 __ __}}}}}})
    (\o c1 _ c2 _ nc0 _ st10 nst0 os0 _ nac0 _ ->
    let {b = interpretObs st10 o os0} in
    case b of {
     True ->
      eq_rec_r st10 (\_ ->
        eq_rec_r c1 (\_ ->
          eq_rec_r Nil
            (eq_rec_r st10 (\_ ->
              eq_rec_r c1 (\_ -> eq_rec_r Nil (\_ -> Left) nac0 __) nc0 __)
              nst0 __) nac0) nc0) nst0 __ __;
     False ->
      eq_rec_r st10 (\_ ->
        eq_rec_r c2 (\_ ->
          eq_rec_r Nil
            (eq_rec_r st10 (\_ ->
              eq_rec_r c2 (\_ -> eq_rec_r Nil (\_ -> Left) nac0 __) nc0 __)
              nst0 __) nac0) nc0) nst0 __ __})
    (\o t _ _ _ _ _ _ st10 _ os0 _ _ _ ->
    let {b = expired (blockNumber os0) t} in
    case b of {
     True -> Left;
     False ->
      let {b0 = interpretObs st10 o os0} in
      case b0 of {
       True -> Left;
       False -> Right}}) c nc inp st9 nst os ac nac __

stepAllaux4 :: InputT -> OST -> StateT -> Contract -> AS -> ((Prod
               (Prod StateT Contract) AS) -> () -> Prod
               (Prod StateT Contract) AS) -> StateT -> Contract -> AS -> Prod
               (Prod StateT Contract) AS
stepAllaux4 com os st9 con ac f nst ncon nac =
  case step_order con ncon com st9 nst os ac nac of {
   Left -> f (Pair (Pair nst ncon) (app ac nac)) __;
   Right -> Pair (Pair st9 con) ac}

stepAllaux3 :: InputT -> OST -> StateT -> Contract -> AS -> ((Prod
               (Prod StateT Contract) AS) -> () -> Prod
               (Prod StateT Contract) AS) -> Prod (Prod StateT Contract) 
               AS
stepAllaux3 com os st9 con ac f =
  stepAllaux4 com os st9 con ac f (fst (fst (step com st9 con os)))
    (snd (fst (step com st9 con os))) (snd (step com st9 con os))

stepAllaux2 :: InputT -> OST -> (Prod (Prod StateT Contract) AS) -> ((Prod
               (Prod StateT Contract) AS) -> () -> Prod
               (Prod StateT Contract) AS) -> Prod (Prod StateT Contract) 
               AS
stepAllaux2 com os x f =
  case x of {
   Pair p0 ac ->
    case p0 of {
     Pair st9 con -> stepAllaux3 com os st9 con ac f}}

stepAllaux :: InputT -> StateT -> Contract -> OST -> AS -> Prod
              (Prod StateT Contract) AS
stepAllaux com st9 con os ac =
  fix (stepAllaux2 com os) (Pair (Pair st9 con) ac)

stepAll :: InputT -> StateT -> Contract -> OST -> Prod (Prod StateT Contract)
           AS
stepAll com st9 con os =
  stepAllaux com st9 con os Nil

addNewChoices :: (Prod SCH_MAP_TYPE AS) -> (Prod IdentChoiceT Person) ->
                 ConcreteChoice -> Prod SCH_MAP_TYPE AS
addNewChoices acc cp choice_int =
  case acc of {
   Pair recorded_choices action_list ->
    case cp of {
     Pair choice_id person ->
      case mem16 (Pair choice_id person) recorded_choices of {
       True -> Pair recorded_choices action_list;
       False -> Pair
        (add19 (Pair choice_id person) choice_int recorded_choices) (Cons
        (ChoiceMade choice_id person choice_int) action_list)}}}

recordChoices :: InputT -> SCH_MAP_TYPE -> Prod SCH_MAP_TYPE AS
recordChoices input recorded_choices =
  case input of {
   Input _ _ _ ic0 ->
    fold_left (\x h -> case h of {
                        Pair p c -> addNewChoices x p c}) (elements10 ic0)
      (Pair recorded_choices Nil)}

isExpiredNotRedeemed :: Timeout -> CCStatus -> Bool
isExpiredNotRedeemed e ccs =
  case ccs of {
   Pair _ c -> case c of {
                NotRedeemed _ ee -> expired e ee;
                _ -> False}}

isClaimed :: InputT -> IdentCCT -> CCStatus -> Bool
isClaimed inp ident status =
  case status of {
   Pair p c ->
    case c of {
     NotRedeemed val _ -> mem4 (RC ident p val) (rc inp);
     _ -> False}}

expiredAndClaimed :: InputT -> Timeout -> IdentCCT -> CCStatus -> Bool
expiredAndClaimed inp et k v =
  andb (isExpiredNotRedeemed et v) (isClaimed inp k v)

extractFromSCMap :: (IdentCCT -> CCStatus -> Bool) -> SC_MAP_TYPE -> Prod
                    (List (Prod IdentCCT CCStatus)) SC_MAP_TYPE
extractFromSCMap f scmap =
  fold_left (\acc el ->
    case acc of {
     Pair t m ->
      case el of {
       Pair ident status ->
        case f ident status of {
         True -> Pair (Cons (Pair ident status) t) (remove13 ident m);
         False -> Pair t m}}}) (elements13 scmap) (Pair Nil scmap)

markRedeemed :: CCStatus -> CCStatus
markRedeemed status =
  case status of {
   Pair p _ -> Pair p ExpiredAndRedeemed}

expireCommits :: InputT -> SC_MAP_TYPE -> OST -> Prod SC_MAP_TYPE AS
expireCommits inp scf os =
  case extractFromSCMap (expiredAndClaimed inp (blockNumber os)) scf of {
   Pair expi nsc -> Pair
    (fold_left (\acc el -> case el of {
                            Pair key val -> add16 key val acc})
      (map (\el ->
        case el of {
         Pair ident status -> Pair ident (markRedeemed status)}) expi) nsc)
    (fold_left (\acc el ->
      case el of {
       Pair ident status ->
        case status of {
         Pair p crstatus ->
          case crstatus of {
           NotRedeemed val _ -> Cons (ExpiredCommitRedeemed ident p val) acc;
           _ -> acc}}}) expi Nil)}

toNormalList :: List a -> [a]
toNormalList (Cons a b) = (a:(toNormalList b))
toNormalList (Nil) = []

fromNormalList :: [a] -> List a
fromNormalList (a:b) = (Cons a (fromNormalList b))
fromNormalList [] = Nil

stepBlock :: InputT -> StateT -> Contract -> OST -> Prod
             (Prod StateT Contract) AS
stepBlock inp st9 con os =
  case recordChoices inp (sch st9) of {
   Pair nsch chas ->
    case expireCommits inp (sc st9) os of {
     Pair nsc pas ->
      case stepAll inp (State nsc nsch) con os of {
       Pair res ras -> Pair res (app chas (app pas ras))}}}

stepBlockWrap :: InputT -> StateT -> Contract -> OST -> (StateT, Contract, [Action])
stepBlockWrap inp sta c os = (nsta, ncon, toNormalList nac)
  where Pair (Pair nsta ncon) nac = stepBlock inp sta c os

foldableStepBlock :: (Prod (Prod (Prod StateT Contract) OST) AS) -> InputT ->
                     Prod (Prod (Prod StateT Contract) OST) AS
foldableStepBlock acc inp =
  case acc of {
   Pair p a ->
    case p of {
     Pair p0 o ->
      case p0 of {
       Pair s c ->
        case stepBlock inp s c o of {
         Pair p1 a0 -> Pair (Pair p1 ((Prelude.+) o ((\x -> x) 1)))
          (app a a0)}}}}

emptyFSBAcc :: Contract -> Prod (Prod (Prod StateT Contract) OST) AS
emptyFSBAcc c =
  Pair (Pair (Pair emptyState c) emptyOS) Nil

executeConcreteTrace :: Contract -> (List InputT) -> Prod
                        (Prod (Prod StateT Contract) OST) AS
executeConcreteTrace c inp =
  fold_left foldableStepBlock inp (emptyFSBAcc c)

executeConcreteTraceWrap :: Contract -> [InputT] -> (StateT, Contract, OST, [Action])
executeConcreteTraceWrap c inp = (nsta, ncon, nos, toNormalList nac)
  where Pair (Pair (Pair nsta ncon) nos) nac = executeConcreteTrace c (fromNormalList inp)

composeInput cc0 rc0 rp0 ic =
  Input (Data.List.foldl' (\m e -> add4 e m) emptyCCSet cc0)
        (Data.List.foldl' (\m e -> add7 e m) emptyRCSet rc0)
        (Data.List.foldl' (\m e -> case e of {
                            ((k1, k2), v) -> add10 (Pair k1 k2) v m}) emptyRPMap rp0)
        (Data.List.foldl' (\m e -> case e of {
                            ((k1, k2), v) -> add13 (Pair k1 k2) v m}) emptyICMap ic)

