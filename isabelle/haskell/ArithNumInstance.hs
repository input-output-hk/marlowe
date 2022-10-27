module ArithNumInstance where

import Arith (Int(..))
import qualified Arith

-- The Num instance for Arith.Int improves the API of using the generated
-- isabelle code. Without this instance, every time you need to add a constant
-- value or timeout, you need to add `Int_of_integer`.
instance Num Arith.Int where
   (Int_of_integer a) + (Int_of_integer b) = Int_of_integer (a + b)
   (Int_of_integer a) * (Int_of_integer b) = Int_of_integer (a * b)
   (Int_of_integer a) - (Int_of_integer b) = Int_of_integer (a - b)
   negate (Int_of_integer a) = Int_of_integer (negate a)
   abs (Int_of_integer a) = Int_of_integer (abs a)
   signum (Int_of_integer a) = Int_of_integer (signum a)
   fromInteger x = Int_of_integer x
