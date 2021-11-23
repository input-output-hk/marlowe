module Language.Marlowe.ExtendedBuilder(ExtendedBuilder, singleton, Language.Marlowe.ExtendedBuilder.length, byteString) where

import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString as ByteString
import Data.Word (Word8)
import Data.ByteString.Char8 (ByteString)

data ExtendedBuilder = ExtendedBuilder Builder Int

instance Semigroup ExtendedBuilder where
  (ExtendedBuilder builder1 length1) <> (ExtendedBuilder builder2 length2) = ExtendedBuilder (builder1 <> builder2) (length1 + length2)

instance Monoid ExtendedBuilder where
  mempty = ExtendedBuilder mempty 0
  mappend = (<>)
  mconcat = foldr mappend mempty

singleton :: Word8 -> ExtendedBuilder
singleton w = ExtendedBuilder (Builder.byteString $ ByteString.singleton w) 1

length :: ExtendedBuilder -> Int
length (ExtendedBuilder _ l) = l

byteString :: ByteString -> ExtendedBuilder
byteString bs = ExtendedBuilder (Builder.byteString bs) (ByteString.length bs)

