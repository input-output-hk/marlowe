{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Marlowe.Spec.Reproducible where

import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.State (MonadState (..), StateT, evalStateT, gets)
import qualified Data.Aeson as JSON
import Marlowe.Spec.Interpret (InterpretJsonRequest, Request, Response)
import Marlowe.Utils (showAsJson)
import QuickCheck.GenT (GenT, runGenT)
import qualified System.Random as Gen
import Test.QuickCheck (Property, Testable (..), arbitrarySizedBoundedIntegral, counterexample, ioProperty, resize)
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.Monadic (PropertyM, assert, monadic', monitor, run)
import Test.QuickCheck.Random (QCGen, mkQCGen)
import Test.Tasty (TestName, TestTree)
import Test.Tasty.QuickCheck (testProperty)

newtype ReproducibleTest a = ReproducibleTest (StateT QCGen IO a)
  deriving (Functor, Applicative, Monad, MonadState QCGen, MonadIO)

runReproducibleTest :: Int -> ReproducibleTest a -> IO a
runReproducibleTest seed (ReproducibleTest m) = do
  let
    qcGen = mkQCGen seed
  evalStateT m qcGen

generate :: MonadState QCGen m => Gen a -> m a
generate (MkGen g) = do
  (oldGen, newGen) <- gets Gen.split
  put newGen
  return (g oldGen 30)

generateT :: (MonadState QCGen m, MonadIO m) => GenT IO a -> m a
generateT gt = do
  (oldGen, newGen) <- gets Gen.split
  put newGen
  let
    MkGen iog = runGenT gt
  liftIO $ iog oldGen 30

assertResponse :: MonadIO m => InterpretJsonRequest -> Request JSON.Value -> Response JSON.Value -> PropertyM m ()
assertResponse interpret req successResponse = do
  res <- run $ liftIO $ interpret req
  monitor (
      counterexample $
          "Request: " ++ showAsJson req ++ "\n" ++
          "Expected: " ++ show successResponse ++ "\n" ++
          "Actual: " ++ show res
      )
  assert $ successResponse == res

reproducibleProperty' :: TestName -> (a -> Property) -> PropertyM ReproducibleTest a -> TestTree
reproducibleProperty' testName tx prop =
  testProperty testName $ runProperty =<< arbitrarySeed
  where
  arbitrarySeed :: Gen Int
  arbitrarySeed = resize 10000 arbitrarySizedBoundedIntegral

  prop' :: PropertyM ReproducibleTest Property
  prop' = tx <$> prop

  runProperty ::  Int -> Gen Property
  runProperty seed = ioProperty . runReproducibleTest seed <$> monadic' prop'

reproducibleProperty :: Testable a => TestName -> PropertyM ReproducibleTest a -> TestTree
reproducibleProperty testName = reproducibleProperty' testName property
