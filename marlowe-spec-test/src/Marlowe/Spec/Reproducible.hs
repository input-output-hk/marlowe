{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Marlowe.Spec.Reproducible where
import Test.QuickCheck.Random (mkQCGen, QCGen)
import Control.Monad.State (StateT, evalStateT, MonadState)
import Control.Monad.IO.Class (MonadIO(..))
import qualified System.Random as Gen
import Control.Monad.State (MonadState (get, put))
import QuickCheck.GenT (GenT, runGenT)
import Test.QuickCheck (Testable, Property, arbitrarySizedBoundedIntegral, resize, ioProperty)
import Test.QuickCheck.Gen (Gen(..))
import Test.Tasty (TestName, TestTree)
import Test.QuickCheck.Monadic (PropertyM, monadic')
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
  (oldGen, newGen) <- Gen.split <$> get
  put newGen
  return (g oldGen 30)


generateT :: (MonadState QCGen m, MonadIO m) => GenT IO a -> m a
generateT gt = do
  (oldGen, newGen) <- Gen.split <$> get
  put newGen
  let
    MkGen iog = runGenT gt
  liftIO $ iog oldGen 30


reproducibleProperty :: Testable a => TestName -> PropertyM ReproducibleTest a -> TestTree
reproducibleProperty testName prop =
  testProperty testName $ runProperty <$> arbitrarySeed
  where
  arbitrarySeed :: Gen Int
  arbitrarySeed = resize 10000 arbitrarySizedBoundedIntegral

  runProperty ::  Int -> Gen Property
  runProperty seed = ioProperty <$> runReproducibleTest seed <$> monadic' prop