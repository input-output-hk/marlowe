module LogicDefs(collectVars, Logic(..), Equation(..), EquationTerm(..), getVar) where

import Data.List (foldl', nub) 

-- Symbolic reasoning

data EquationTerm a = NegVar a | Var a | Const Integer
 deriving (Eq, Ord, Show, Read)
data Equation a = LE [EquationTerm a] [EquationTerm a]
 deriving (Eq, Ord, Show, Read)
data Logic a = Eq (Equation a) | Not (Logic a) | And [Logic a] | Or [Logic a]
 deriving (Eq, Ord, Show, Read)

isVar :: EquationTerm a -> Bool
isVar (NegVar _) = True
isVar (Var _) = True
isVar _ = False

getVar :: EquationTerm a -> a
getVar (NegVar x) = x
getVar (Var x) = x
getVar _ = error "getVar: not a var!"

-- Combination of symbolic reasoning and eq solving
collectVarsEq :: Equation a -> [a]
collectVarsEq (LE l1 l2) = map getVar $ filter isVar (l1 ++ l2)

collectVarsLogic :: Logic a -> [a]
collectVarsLogic (Eq x) = collectVarsEq x
collectVarsLogic (Not l) = collectVarsLogic l
collectVarsLogic (And l) = foldl' (++) [] $ map collectVarsLogic l
collectVarsLogic (Or l) = foldl' (++) [] $ map collectVarsLogic l

collectVars :: Eq a => Logic a -> [a]
collectVars l = nub $ collectVarsLogic l

