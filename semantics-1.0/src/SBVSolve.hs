module SBVSolve(solveLogic) where

import Data.SBV
import Data.SBV.Internals (SMTModel(..), CW(..), CWVal(..))
import LogicDefs
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (liftM, mapM)
import Data.List (foldl')
import qualified Data.Map as M

-- Symbolic reasoning

termToSat :: Ord a => M.Map a SInteger -> EquationTerm a -> Symbolic SInteger
termToSat _ (Const x) = do return ((fromIntegral x) :: SInteger)
termToSat m (Var a) = return (m M.! a)
termToSat m (NegVar a) = return (- (m M.! a))

eqToSat :: Ord a => M.Map a SInteger -> Equation a -> Symbolic SBool
eqToSat m (LE t1 t2) = do x <- p_term t1
                          y <- p_term t2
                          return $ x .<= y
  where p_term t = liftM (foldl' (\a b -> a + b) (0 :: SInteger)) $ mapM (termToSat m) t

logicToSat :: Ord a => M.Map a SInteger -> LogicDefs.Logic a -> Symbolic SBool
logicToSat m (Eq x) = eqToSat m x 
logicToSat m (Not l) = do x <- logicToSat m l; return $ bnot x
logicToSat m (And l) = do x <- mapM (logicToSat m) l; return $ bAnd x
logicToSat m (Or l) = do x <- mapM (logicToSat m) l; return $ bOr x

allocateVars :: Ord a => Show a => [a] -> Symbolic (M.Map a SInteger)
allocateVars l = do x <- sIntegers (map show l)
                    return $ M.fromList $ zip l x

solveLogic :: Show a => Ord a => Read a => LogicDefs.Logic a -> Maybe [(a, Integer)]
solveLogic l =
  unsafePerformIO (
     do (SatResult res) <- sat $ do {x <- allocateVars (collectVars l); logicToSat x l}
        return $ case res of
                   Unsatisfiable _ _ -> Nothing
                   Satisfiable _ (SMTModel {modelAssocs = lr}) -> Just [(read stri, x) | (stri, CW {cwVal = CWInteger x}) <- lr]
                   e -> error "Could not determine whether the trace is satisfiable in solveLogic"
  )

