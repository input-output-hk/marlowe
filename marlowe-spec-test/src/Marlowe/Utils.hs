module Marlowe.Utils  where

import Data.Aeson (encode)
import qualified Data.Text.Lazy as LT
import Data.Text.Lazy.Encoding (decodeUtf8)
import qualified Data.Aeson as JSON
import Data.Aeson.Types (ToJSON (..))

showJson :: JSON.Value -> String
showJson = LT.unpack . decodeUtf8 . encode

showAsJson :: ToJSON a => a -> String
showAsJson = showJson . toJSON
