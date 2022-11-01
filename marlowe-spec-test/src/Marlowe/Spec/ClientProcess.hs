{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.ClientProcess
 ( ClientProcess(..)
 , CliPath(..)
 , TraceCP
 , sendJsonRequest
 , parseJsonResponse
 , withClientProcess
 , eval
 )
where

import Data.ByteString.Lazy.Char8 (hPutStrLn)
import qualified Data.ByteString.Lazy.Char8 as C
import System.Process (CreateProcess(..), StdStream(..), ProcessHandle, proc, createProcess)
import System.IO (hSetBuffering, hGetLine,BufferMode(..))
import qualified Data.Aeson.Types as JSON
import qualified Data.Aeson as JSON
import GHC.IO.Handle (Handle)
import Test.Tasty (TestTree, withResource, askOption)
import Marlowe.Spec.Interpret (Request(..), Response(..))
import Data.Data (Typeable)
import Test.Tasty.Options (IsOption(..), mkOptionCLParser, mkFlagCLParser, safeReadBool)
import Options.Applicative (short)
import Options.Applicative.Builder (metavar)
import Test.Tasty.HUnit (assertFailure)
import GHC.Base (when)

data ClientProcess =
  ClientProcess
    { stdInH  :: Handle
    , stdOutH :: Handle
    , procH   :: ProcessHandle
    , traceCP :: Bool
    }

sendJsonRequest :: ClientProcess -> Request JSON.Value -> IO ()
sendJsonRequest cp r = do
  let
    h = stdInH cp
    encodedReq = JSON.encode r
  hPutStrLn h "```"
  hPutStrLn h encodedReq
  hPutStrLn h "```"
  when (traceCP cp) $ putStrLn $ "Send JSON request: " ++ C.unpack encodedReq

parseJsonResponse :: ClientProcess -> IO (Maybe (Response JSON.Value))
parseJsonResponse cp = do
  let
    h = stdOutH cp
  line <- hGetLine h
  let
    mRes = JSON.decode $ C.pack line
  when (traceCP cp) $ putStrLn $ "Parse JSON response: " ++ show mRes
  return mRes


data CliPath
  = UndefinedCliPath
  | CliPath FilePath
  deriving (Show, Eq, Typeable)

instance IsOption CliPath where
  defaultValue = UndefinedCliPath
  parseValue str = pure $ CliPath str
  optionName = return "cli-path"
  optionHelp = return "Path to the client application to test"
  optionCLParser = mkOptionCLParser (short 'c' <> metavar "CLI_PATH")


newtype TraceCP = TraceCP Bool
  deriving (Show, Eq, Typeable)


instance IsOption TraceCP where
  defaultValue = TraceCP False
  parseValue str = TraceCP <$> safeReadBool str
  optionName = return "trace-cp"
  optionHelp = return "Trace client process"
  optionCLParser = mkFlagCLParser mempty (TraceCP True)

withClientProcess :: (IO ClientProcess -> TestTree) -> TestTree
withClientProcess testCreator =
  askOption
    (\cliPathOpt ->
      askOption
        (\traceOpt -> withClientProcess' traceOpt cliPathOpt
        )
    )

  where
  withClientProcess' (TraceCP traceOpt) cliPathOpt =
    withResource
      (do
        cliCmd <- case cliPathOpt of
          UndefinedCliPath -> fail "Undefined cli path"
          CliPath p -> return p
        when traceOpt $ putStrLn $ "Create client process with path: " ++ show cliCmd

        (Just hIn, Just hOut, _, ph) <- createProcess
            (proc cliCmd [])
            { std_in  = CreatePipe
            , std_out = CreatePipe
            }
        hSetBuffering hIn  LineBuffering
        hSetBuffering hOut LineBuffering
        return $ ClientProcess
          { stdInH  = hIn
          , stdOutH = hOut
          , procH   = ph
          , traceCP = traceOpt
          }
      )
      (\_ -> pure ())
      testCreator

eval :: IO ClientProcess -> Request JSON.Value -> IO (Response JSON.Value)
eval getCP req = do
  cp <- getCP
  sendJsonRequest cp req
  mRes <- parseJsonResponse cp
  case mRes of
    Nothing -> assertFailure "Could not parse response from the client cli"
    Just res -> return res
