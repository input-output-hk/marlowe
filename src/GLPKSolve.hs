module GLPKSolve(solveLEInt) where

import Data.Map((!))
import Data.List(genericLength)
import Data.LinearProgram.GLPK.Solver (msgLev, MsgLev (MsgOff), mipDefaults, glpSolveVars)
import Data.LinearProgram.Common (LP)
import Control.Monad.LPMonad (LPM, setDirection, setObjective, setVarKind, execLPM, leqTo, varLeq, varGeq)
import Data.LinearProgram.Common(linCombination, VarKind(IntVar), Direction(Min) )
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (forM_)

lpm :: [[Double]] -> [String] -> LPM String Double ()
lpm [] labels = do setDirection Min
                   setObjective $ linCombination [(0, l) | l <- labels]
                   forM_ labels (`setVarKind` IntVar) 
                   forM_ labels (`varLeq` 1000) -- Set upper bound so that solver does not hang
                   forM_ labels (`varGeq` (-1000)) -- Set lower bound so that solver does not hang
lpm (h:t) labels = do leqTo (linCombination $ zip i labels) l
                      lpm t labels
 where
   (i, l) = (init h, last h)

solveLEIntAux :: [[Double]] -> Maybe [Double]
solveLEIntAux [] = Just []
solveLEIntAux l@(h:_) =
  case unsafePerformIO $ glpSolveVars (mipDefaults {msgLev = MsgOff}) $ execLPM $ lpm l labels of
    (_, Nothing) -> Nothing
    (_, Just (_, m)) -> Just $ map (m !) labels
  where labels = map show [1..(genericLength h)]

solveLEInt :: Eq a => Eq b => ([[Rational]], [a], [b]) -> Maybe [(b, Integer)]
solveLEInt (m, r, c) =
  case solveLEIntAux nm of
    Just x -> Just $ zip c $ map round x
    Nothing -> Nothing
  where nm = map (map (fromRational)) m

