module Language.Marlowe.Serialisation(positiveIntToByteString, packByteString, intToByteString, listToByteString) where
import Language.Marlowe.ExtendedBuilder (ExtendedBuilder)
import qualified Language.Marlowe.ExtendedBuilder as EBSB

positiveIntToByteString :: Integer -> ExtendedBuilder
positiveIntToByteString x =
  if x < 128 then EBSB.singleton (toEnum (fromIntegral x))
   else EBSB.singleton (toEnum (fromIntegral (x `mod` 128 + 128))) <>
          positiveIntToByteString (x `div` 128 - 1)

packByteString :: ExtendedBuilder -> ExtendedBuilder
packByteString bs = positiveIntToByteString (fromIntegral $ EBSB.length bs) <> bs

intToByteString :: Integer -> ExtendedBuilder
intToByteString x =
   if 0 <= x
   then positiveIntToByteString (x * 2)
   else positiveIntToByteString (- (x * 2 + 1))

listToByteString :: (a -> ExtendedBuilder) -> [a] -> ExtendedBuilder
listToByteString f l =
  positiveIntToByteString (fromIntegral (length l)) <> listToByteStringAux f l
  where listToByteStringAux :: (a -> ExtendedBuilder) -> [a] -> ExtendedBuilder
        listToByteStringAux f = foldr ((<>) . f) mempty

