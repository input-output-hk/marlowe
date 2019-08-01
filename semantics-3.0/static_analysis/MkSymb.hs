{-# LANGUAGE TemplateHaskell #-}
module MkSymb where

import Data.List (foldl')
import Language.Haskell.TH as TH
import Data.Either (Either(..))

nestClauses :: [Con] -> TypeQ
nestClauses [] = error "No constructors for type" 
nestClauses [NormalC _ params] =
  foldl' (appT) (tupleT (length params)) [return t | (_, t) <- params]
nestClauses list = appT (appT [t| Either |]
                              (nestClauses fHalf))
                        (nestClauses sHalf)
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkNestedDec :: TH.Name -> [Con] -> TH.Q TH.Dec
mkNestedDec nName clauses =
  tySynD nName [] $ nestClauses clauses

nestFunClauses :: [Con] -> (ExpQ -> ExpQ) -> [ClauseQ]
nestFunClauses [] f = error "No constructors for type"
nestFunClauses [NormalC name params] f =
  [do names <- mapM (\x -> newName ('p':(show x))) [1..(length params)]
      clause [ conP name [ varP n | n <- names ] ]
             (normalB (f (tupE (map varE names)))) []]
nestFunClauses list f = (nestFunClauses fHalf (f . (\x -> [e| Left $(x) |]))) ++
                        (nestFunClauses sHalf (f . (\x -> [e| Right $(x) |])))
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkNestFunc :: String -> TH.Name -> TH.Name -> [Con] -> TH.Q [TH.Dec]
mkNestFunc typeBaseName typeName typeNName clauses =
  do let nestFunName = ("nest" ++ typeBaseName)
     let nfName = mkName nestFunName
     signature <- sigD nfName (appT (appT arrowT (conT typeName))
                                         (conT typeNName))
     declaration <- funD nfName $ nestFunClauses clauses id
     return [signature, declaration]

mkSymbolicDatatype :: TH.Name -> TH.Q [TH.Dec]
mkSymbolicDatatype typeName =
  do TyConI (DataD _ _ _ _ clauses _) <- reify typeName
     let typeBaseName = nameBase typeName
     let nName = mkName ('N':typeBaseName)
     nestedDecl <- mkNestedDec nName clauses
     nestFunc <- mkNestFunc typeBaseName typeName nName clauses
     return (nestedDecl:nestFunc)

