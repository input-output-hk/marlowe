module ArithNumInstance where

import Arith (Int(..))
import qualified Arith

instance Num Arith.Int where
   (Int_of_integer a) + (Int_of_integer b) = Int_of_integer (a + b)
   (Int_of_integer a) * (Int_of_integer b) = Int_of_integer (a * b)
   (Int_of_integer a) - (Int_of_integer b) = Int_of_integer (a - b)
   negate (Int_of_integer a) = Int_of_integer (negate a)
   abs (Int_of_integer a) = Int_of_integer (abs a)
   signum (Int_of_integer a) = Int_of_integer (signum a)
   fromInteger x = Int_of_integer x
