{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

module Marlowe.Spec.ClientProcess
  ( CliPath (..),
    TraceCP,
    PoolSize,
    sendJsonRequest,
    parseJsonResponse,
    withClientProcess,
    eval,
  )
where

import Control.Concurrent.STM (atomically)
import Control.Concurrent.STM.TQueue (TQueue, newTQueue, readTQueue, writeTQueue)
import Control.Monad (forM, forM_)
import qualified Data.Aeson as JSON
import Data.ByteString.Lazy.Char8 (hPutStrLn)
import qualified Data.ByteString.Lazy.Char8 as C
import Data.Data (Typeable)
import GHC.IO.Handle (Handle)
import GHC.IO.IOMode (IOMode (..))
import Marlowe.Spec.Interpret (Request (..), Response (..))
import Options.Applicative (short)
import Options.Applicative.Builder (metavar)
import System.IO (BufferMode (..), hGetLine, hSetBuffering, openFile)
import System.Process (CreateProcess (..), ProcessHandle, StdStream (..), createProcess, proc)
import System.Timeout (timeout)
import Test.Tasty (TestTree, askOption, withResource)
import Test.Tasty.Options (IsOption (..), mkOptionCLParser, safeRead)

type ClientProcessId = Int

data ClientProcess =
  ClientProcess
    { stdInH  :: Handle           -- ^ File handle to send requests to a Client Process
    , stdOutH :: Handle           -- ^ File handle to receive responses from the Client Process
    , traceH  :: Maybe Handle     -- ^ File handle to put debug information
    , procH   :: ProcessHandle    -- ^ Process handle to control the client process
    , cpId    :: ClientProcessId  -- ^ Internal client process id
    }

data ClientProcessPool =
  ClientProcessPool
    { threadPool      :: TQueue ClientProcess
    , cliCmd          :: FilePath
    }

sendJsonRequest :: ClientProcess -> Request JSON.Value -> IO ()
sendJsonRequest cp r = do
  let
    encodedReq = JSON.encode r
    h = stdInH cp
    debugH = traceH cp
    pid = cpId cp

  hPutStrLn h "```"
  hPutStrLn h encodedReq
  hPutStrLn h "```"
  debug debugH $ show pid ++ " - Send JSON request: " ++ C.unpack encodedReq

parseJsonResponse :: ClientProcess -> IO (Response JSON.Value)
parseJsonResponse cp = do
  let
    h = stdOutH cp
    debugH = traceH cp
    pid = cpId cp
  mLine <- timeout 5000000 $ hGetLine h
  let
    res = case mLine of
      Nothing -> RequestTimeOut
      Just line -> case JSON.decode $ C.pack line of
        Nothing -> ResponseFailure  "Could not parse response from the client cli"
        Just r -> r

  debug debugH $ show pid ++ " - Parse JSON response: " ++ C.unpack (JSON.encode res)
  return res

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

newtype TraceCP = TraceCP (Maybe FilePath)
  deriving (Show, Eq, Typeable)

instance IsOption TraceCP where
  defaultValue = TraceCP Nothing
  parseValue str = Just $ TraceCP $ Just str
  optionName = return "trace-cp"
  optionHelp = return "If provided, filepath of the client process trace log"
  optionCLParser = mkOptionCLParser (metavar "TRACE_CP")

newtype PoolSize = PoolSize Int
  deriving (Show, Eq, Typeable)

instance IsOption PoolSize where
  defaultValue = PoolSize 10
  parseValue str = PoolSize <$> safeRead str
  optionName = return "pool-size"
  optionHelp = return "Number of client process to spawn (default 10)"
  optionCLParser = mkOptionCLParser (metavar "POOL_SIZE")

withThreadProcess :: ClientProcessPool -> (ClientProcess -> IO a) -> IO a
withThreadProcess clientProcess callback = do
  let
    pool = threadPool clientProcess
  threadProcess <- atomically $ readTQueue pool

  res <- callback threadProcess
  atomically $ writeTQueue pool threadProcess

  pure res

debug :: Maybe Handle -> String -> IO ()
debug mh str = forM_ mh (\h -> hPutStrLn h $ C.pack str)

createThreadProcess :: Int -> FilePath -> Maybe Handle -> IO ClientProcess
createThreadProcess pid cliPath debugH = do
  debug debugH $ show pid ++ " - Create client process with path: " ++ show cliPath

  (Just hIn, Just hOut, _, ph) <- createProcess
            (proc cliPath [])
            { std_in  = CreatePipe
            , std_out = CreatePipe
            }
  hSetBuffering hIn  LineBuffering
  hSetBuffering hOut LineBuffering
  pure
      ClientProcess
        { stdInH  = hIn
        , stdOutH = hOut
        , procH   = ph
        , cpId    = pid
        , traceH  = debugH
        }

withClientProcess :: (IO ClientProcessPool -> TestTree) -> TestTree
withClientProcess testCreator =
  askOption
    (\cliPathOpt ->
      askOption
        (\traceOpt ->
          askOption
            (\poolSize ->
              withClientProcess' traceOpt cliPathOpt poolSize
            )
        )
    )

  where
  withClientProcess' (TraceCP tracePath) cliPathOpt (PoolSize poolSize) =
    withResource
      (do
        cliPath <- case cliPathOpt of
          UndefinedCliPath -> fail "Undefined cli path"
          CliPath p -> return p

        debugH <- forM tracePath
              (\path -> do
                h <- openFile path WriteMode
                hSetBuffering h  LineBuffering
                pure h
              )

        processes <- forM [0..poolSize] \i -> createThreadProcess i cliPath debugH
        handles <- atomically do
          pool <- newTQueue
          forM_ processes $ writeTQueue pool
          pure pool
        return $ ClientProcessPool
          { threadPool = handles
          , cliCmd     = cliPath
          }
      )
      (\_ -> pure ())
      testCreator

eval :: IO ClientProcessPool -> Request JSON.Value -> IO (Response JSON.Value)
eval getCPPool req = do
  cpPool <- getCPPool
  withThreadProcess cpPool
    (\cp -> do
      sendJsonRequest cp req
      parseJsonResponse cp
    )
