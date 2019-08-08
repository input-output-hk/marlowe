{-# LANGUAGE TemplateHaskell #-}
module MkSymb where

import Data.SBV
import Data.SBV.Tuple as ST
import Data.SBV.Either as SE
import Data.List (foldl', foldl1')
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

mkSymDec :: TH.Name -> TH.Name -> TH.Q TH.Dec
mkSymDec sName nName =
  tySynD sName [] $ [t| SBV $(conT nName) |]

mkSubSymDec :: TH.Name -> [Con] -> TH.Q TH.Dec
mkSubSymDec ssName clauses =
  dataD (return [])
        ssName
        [] Nothing [ normalC (let typeBaseName = nameBase name in
                              mkName ('S':'S':typeBaseName))
                             [ bangType (return pb)
                                        [t| SBV $(return param) |]
                              | (pb, param) <- params ]
                    | NormalC name params <- clauses ]
        []

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

unNestFunClauses :: [Con] -> (PatQ -> PatQ) -> [ClauseQ]
unNestFunClauses [] f = error "No constructors for type"
unNestFunClauses [NormalC name params] f =
  [do names <- mapM (\x -> newName ('p':(show x))) [1..(length params)]
      clause [f (tupP (map varP names))]
             (normalB (foldl' appE (conE name) [ varE n | n <- names ])) []]
unNestFunClauses list f = (unNestFunClauses fHalf (f . (\x -> [p| Left $(x) |]))) ++
                          (unNestFunClauses sHalf (f . (\x -> [p| Right $(x) |])))
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkUnNestFunc :: String -> TH.Name -> TH.Name -> [Con] -> TH.Q [TH.Dec]
mkUnNestFunc typeBaseName typeName typeNName clauses =
  do let unNestFunName = ("unNest" ++ typeBaseName)
     let unfName = mkName unNestFunName
     signature <- sigD unfName (appT (appT arrowT (conT typeNName))
                                           (conT typeName))
     declaration <- funD unfName $ unNestFunClauses clauses id
     return [signature, declaration]

mkSymCaseRec :: Name -> [Con] -> ExpQ
mkSymCaseRec func [] = error "No constructors for type"
mkSymCaseRec func [NormalC name params] =
  do paramNames <- mapM (\x -> newName ('p':(show x))) [1..(length params)]
     let ssName = mkName ('S':'S':(nameBase name))
     let wrapping = [e| (\ $(tupP $ map varP paramNames) ->
                        $(varE func)
                        ($(foldl' (appE) (conE ssName) $ map (varE) paramNames))) |]
     if length params > 1
     then [e| $(wrapping) . ST.untuple |]
     else if (length params > 0)
          then wrapping
          else [e| $(wrapping) . (const ()) |]
mkSymCaseRec func list = [e| SE.either $(mkSymCaseRec func fHalf)
                                       $(mkSymCaseRec func sHalf) |]
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkSymCase :: String -> TH.Name -> TH.Name -> [Con] -> TH.Q [TH.Dec]
mkSymCase typeBaseName sName ssName clauses =
  do let symCaseFunName = ("symCase" ++ typeBaseName)
     let scName = mkName symCaseFunName
     typeVar <- newName "a"
     func <- newName "f"
     signature <- sigD scName $ [t| SymVal $(varT typeVar) =>
                                    ($(conT ssName) -> SBV $(varT typeVar))
                                 -> $(conT sName) -> SBV $(varT typeVar) |]
     declaration <- funD scName $
                    [clause [varP func]
                            (normalB (mkSymCaseRec func clauses)) []]
     return [signature, declaration]

mkSymConsts :: TH.Name -> [Con] -> (ExpQ -> ExpQ) -> TH.Q [TH.Dec]
mkSymConsts _ [] f = error "No constructors for type"
mkSymConsts sName [NormalC name params] f =
  do let nestFunName = ("s" ++ (nameBase name))
     let nfName = mkName nestFunName
     signature <- sigD nfName (foldl1' (\x y -> appT (appT arrowT y) x)
                                  ((conT sName):
                                   (reverse [ [t| SBV $(return param) |]
                                             | (_, param) <- params ])))
     declaration <- funD nfName $
       [do names <- mapM (\x -> newName ('p':(show x))) [1..(length params)]
           clause [ varP n | n <- names ]
                  (normalB (f (if length params > 1
                               then [e| ST.tuple $(tupE (map varE names)) |]
                               else if length params > 0
                                    then tupE (map varE names)
                                    else [e| literal () |]))) []]
     return [signature, declaration]
mkSymConsts sName list f =
  do rfHalf <- (mkSymConsts sName fHalf (f . (\x -> [e| sLeft $(x) |])))
     rsHalf <- (mkSymConsts sName sHalf (f . (\x -> [e| sRight $(x) |])))
     return (rfHalf ++ rsHalf)
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkSymbolicDatatype :: TH.Name -> TH.Q [TH.Dec]
mkSymbolicDatatype typeName =
  do TyConI (DataD _ _ _ _ clauses _) <- reify typeName
     let typeBaseName = nameBase typeName
     let sName = mkName ('S':typeBaseName)
     let nName = mkName ('N':typeBaseName)
     let ssName = mkName ('S':'S':typeBaseName)
     nestedDecl <- mkNestedDec nName clauses
     symDecl <- mkSymDec sName nName
     subSymDecl <- mkSubSymDec ssName clauses 
     nestFunc <- mkNestFunc typeBaseName typeName nName clauses
     unNestFunc <- mkUnNestFunc typeBaseName typeName nName clauses
     symCaseFunc <- mkSymCase typeBaseName sName ssName clauses
     symConsts <- mkSymConsts sName clauses id
     return (nestedDecl:symDecl:subSymDecl:
             (nestFunc ++ unNestFunc ++ symCaseFunc ++ symConsts))

