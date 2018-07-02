module LogicSolve(solveLogic) where

import GLPKSolve (solveLEInt)
import Data.List (foldl', genericLength, genericIndex, genericDrop)
import Data.Maybe (isJust, fromJust)
import LogicDefs

-- Symbolic reasoning

isPVar :: EquationTerm a -> Bool
isPVar (Var _) = True
isPVar _ = False

isNVar :: EquationTerm a -> Bool
isNVar (NegVar _) = True
isNVar _ = False

isConst :: EquationTerm a -> Bool
isConst (Const _) = True
isConst _ = False

getConst :: EquationTerm a -> Integer 
getConst (Const x) = x
getConst _ = error "getConst: not a const!"

negateEq :: Equation a -> Equation a
negateEq (LE a b) = (LE (Const 1:b) a)

negateLogic :: Logic a -> Logic a
negateLogic (Eq x) = Eq (negateEq x)
negateLogic (Not l) = l
negateLogic (And l) = Or $ map negateLogic l
negateLogic (Or l) = And $ map negateLogic l

removeNots :: Logic a -> Logic a
removeNots (Eq x) = Eq x
removeNots (Not l) = removeNots (negateLogic l)
removeNots (And l) = And $ map removeNots l
removeNots (Or l) = Or $ map removeNots l

data LogicIdx = IdxChoice Integer LogicIdx
              | IdxAll [LogicIdx]
              | IdxEq
 deriving (Eq, Ord, Show, Read)

idxToSystem :: Logic a -> LogicIdx -> [Equation a]
idxToSystem (Eq x) IdxEq = [x]
idxToSystem (And l1) (IdxAll l2) = concat $ zipWith (idxToSystem) l1 l2
idxToSystem (Or l) (IdxChoice i e) = idxToSystem (l `genericIndex` i) e
idxToSystem (Not _) _ = error "Not node in idxToSystem"
idxToSystem _ _ = error "Index does not match logic in idxToSystem"

stepAnd :: [Logic a] -> [LogicIdx] -> Maybe [LogicIdx]
stepAnd [] [] = Nothing
stepAnd (h1:t1) (h2:t2) =
  case stepIdx h1 h2 of
    Nothing -> case stepAnd t1 t2 of
                 Nothing -> Nothing
                 Just nt2 -> case initialIdx h1 of
                               Just nh1 -> Just (nh1:nt2)
                               Nothing -> Nothing
    Just x -> Just (x:t2)
stepAnd _ _ = error "Different lengths in stepAnd"

stepIdx :: Logic a -> LogicIdx -> Maybe LogicIdx
stepIdx (Eq _) IdxEq = Nothing
stepIdx (And l) (IdxAll l2) =
  case stepAnd l l2 of
    Just x -> Just $ IdxAll x
    Nothing -> Nothing
stepIdx (Or l) (IdxChoice i e) =
  case stepIdx (l `genericIndex` i) e of
    Nothing -> initialIdxOr l2 ni
    Just x -> Just $ (IdxChoice i x)
  where l2 = genericDrop ni l
        ni = i + 1
stepIdx (Not _) _ = error "Not node in stepIdx"
stepIdx _ _ = error "Index does not match logic in stepIdx"

initialIdxOr :: [Logic a] -> Integer -> Maybe LogicIdx
initialIdxOr [] _ = Nothing
initialIdxOr (h:t) i = 
  case initialIdx h of
    Just x -> Just $ IdxChoice i x 
    Nothing -> initialIdxOr t (i + 1)

initialIdx :: Logic a -> Maybe LogicIdx
initialIdx (Eq _) = Just IdxEq
initialIdx (And l)
  | all isJust v = Just $ IdxAll $ map fromJust $ v
  | otherwise = Nothing
  where v = map initialIdx l
initialIdx (Or l) = initialIdxOr l 0
initialIdx (Not _) = error "Not node in initailIdx"

possibilitiesAux :: Logic a -> LogicIdx -> (Maybe LogicIdx, [Equation a])
possibilitiesAux l i = (stepIdx l i, idxToSystem l i) 

expandWithAcc :: (a -> (Maybe a, b)) -> a -> [b]
expandWithAcc f a =
  case f a of
   (Just na, b) -> (b:(expandWithAcc f na))
   (Nothing, b) -> [b]

possibilities :: Logic a -> [[Equation a]]
possibilities l =
  case initialIdx l of
    Nothing -> []
    Just x -> expandWithAcc (possibilitiesAux l) x

add :: (Eq a) => Integer -> [(a, Integer)] -> a -> [(a, Integer)]
add n ((s,v):t) el
 | s == el = (s,v + n):t
 | otherwise = (s,v):(add n t el)
add _ [] _ = [] 

toEquation :: Eq a => [a] -> Logic a -> [Rational]
toEquation syms (Eq (LE l1 l2)) = (map toRational v) ++ [c]
  where csyms = zip syms $ repeat 0
        pl1 = map getVar $ (filter isPVar l1) ++ (filter isNVar l2)
        nl1 = map getVar $ (filter isPVar l2) ++ (filter isNVar l1)
        csyms2 = foldl' (add 1) csyms pl1
        csyms3 = foldl' (add (-1)) csyms2 nl1
        (_,v) = unzip csyms3
        cp = sum (map getConst $ filter isConst l2)
        cn = sum (map getConst $ filter isConst l1)
        c = toRational (cp - cn)
toEquation _ _ = error "Wrong format in toEquation"

toMatrix :: Eq a => Logic a -> ([[Rational]], [Integer], [Maybe a])
toMatrix l@(And c) = (map (toEquation symbols) c, [1..genericLength c], allSymbols)
 where symbols = collectVars l
       allSymbols = (map Just $ symbols) ++ [Nothing]
toMatrix (Eq c) = toMatrix (And [Eq c])
toMatrix _ = error "Wrong format in toMatrix"

getFirstResult :: [Maybe [(Maybe a, Integer)]] -> Maybe [(a, Integer)]
getFirstResult [] = Nothing
getFirstResult ((Nothing):t) = getFirstResult t
getFirstResult ((Just x):_) = Just $ [(e, n) | (Just e, n) <- x]

solveLogic :: Eq a => Logic a -> Maybe [(a, Integer)]
solveLogic l = getFirstResult res
  where
   res = map (solveLEInt . toMatrix . And . (map Eq)) options
   options = possibilities $ removeNots l

