module Language.Marlowe.Deserialisation (byteStringToPositiveInt, getByteString, byteStringToInt, byteStringToList) where

import Data.ByteString (ByteString)
import Data.ByteString as BS(ByteString, length, splitAt, uncons)

byteStringToPositiveInt :: ByteString -> Maybe (Integer, ByteString)
byteStringToPositiveInt bs =
  case BS.uncons bs of
    Nothing -> Nothing
    Just (xw, rest) ->
        let x = fromIntegral (fromEnum xw) :: Integer in
        (if x < 128
         then Just (x, rest)
         else (case byteStringToPositiveInt rest of
                Nothing -> Nothing
                Just (y, extra) ->
                  Just ((x - 128) + (128 * (y + 1)), extra)))

getByteString :: ByteString -> Maybe (ByteString, ByteString)
getByteString bs =
  case byteStringToPositiveInt bs of
   Nothing -> Nothing;
   Just (val, rest) ->
     (if fromIntegral (BS.length rest) < val
      then Nothing
      else Just (BS.splitAt (fromInteger val) rest))

byteStringToInt :: ByteString -> Maybe (Integer, ByteString)
byteStringToInt x =
  case byteStringToPositiveInt x of
   Nothing -> Nothing;
   Just (y, extra) ->
     Just (if even y
           then y `div` 2
           else (- (y `div` 2 + 1)), extra)

byteStringToListAux :: (ByteString -> Maybe (a, ByteString)) -> Integer -> ByteString -> Maybe ([a], ByteString)
byteStringToListAux f n bs =
  if 0 < n
  then case f bs of
          Nothing -> Nothing;
          Just (aa, nbs) -> case byteStringToListAux f (n - 1) nbs of
                              Nothing -> Nothing;
                              Just (lr, fbs) -> Just (aa : lr, fbs);
   else Just ([], bs);

byteStringToList :: (ByteString -> Maybe (a, ByteString)) -> ByteString -> Maybe ([a], ByteString);
byteStringToList f bs = case byteStringToPositiveInt bs of
                         Nothing -> Nothing;
                         Just (aa, b) -> byteStringToListAux f aa b;


