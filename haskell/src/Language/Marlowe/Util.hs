{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Marlowe.Util where
import           Data.List                        (foldl')
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.String                      (IsString(..))
import qualified Data.Text                        as T
import           Language.Marlowe.Semantics       (Payment(..))
import           Language.Marlowe.Semantics.Types (Input, InputContent(IDeposit), Payee(Party), ValueId(..),
                                                   Money, Party(..), getInputContent, Token (Token))
import           Data.Text.Encoding (encodeUtf8)

ada :: Token
ada = Token "" ""

instance IsString Party where
    fromString s = Role (encodeUtf8 $ T.pack s)

instance IsString ValueId where
    fromString s = ValueId (T.pack s)




