module ContractFormatter where

import Semantics
import Data.List (groupBy, intercalate, genericLength, genericReplicate)

------------------------
-- AST dependent code --
------------------------

data ASTNode = ASTNodeC Contract
             | ASTNodeO Observation
             | ASTNodeM Money
             | ASTNodeCC IdentCC
             | ASTNodeIC IdentChoice
             | ASTNodeIP IdentPay
             | ASTNodeI Integer

listCurryType :: ASTNode -> (String, [ASTNode])
listCurryType (ASTNodeM (AvailableMoney identCC))
 = ("AvailableMoney", [ASTNodeCC identCC])
listCurryType (ASTNodeM (AddMoney money1 money2))
 = ("AddMoney", [ASTNodeM money1, ASTNodeM money2])
listCurryType (ASTNodeM (ConstMoney cash))
 = ("ConstMoney", [ASTNodeI cash])
listCurryType (ASTNodeM (MoneyFromChoice identChoice person def))
 = ("MoneyFromChoice", [ASTNodeIC identChoice, ASTNodeI person, ASTNodeM def])
listCurryType (ASTNodeO (BelowTimeout timeout))
 = ("BelowTimeout", [ASTNodeI timeout])
listCurryType (ASTNodeO (AndObs observation1 observation2))
 = ("AndObs", [ASTNodeO observation1, ASTNodeO observation2])
listCurryType (ASTNodeO (OrObs observation1 observation2))
 = ("OrObs", [ASTNodeO observation1, ASTNodeO observation2])
listCurryType (ASTNodeO (NotObs observation))
 = ("NotObs", [ASTNodeO observation])
listCurryType (ASTNodeO (PersonChoseThis identChoice person concreteChoice))
 = ("PersonChoseThis", [ASTNodeIC identChoice, ASTNodeI person, ASTNodeI concreteChoice])
listCurryType (ASTNodeO (PersonChoseSomething identChoice person))
 = ("PersonChoseSomething", [ASTNodeIC identChoice, ASTNodeI person])
listCurryType (ASTNodeO (ValueGE money1 money2))
 = ("ValueGE", [ASTNodeM money1, ASTNodeM money2])
listCurryType (ASTNodeO TrueObs) = ("TrueObs", [])
listCurryType (ASTNodeO FalseObs) = ("FalseObs", [])
listCurryType (ASTNodeC Null) = ("Null", [])
listCurryType (ASTNodeC (CommitCash identCC person cash timeout1 timeout2 contract1 contract2))
 = ("CommitCash", [ASTNodeCC identCC, ASTNodeI person, ASTNodeM cash, ASTNodeI timeout1,
                   ASTNodeI timeout2, ASTNodeC contract1, ASTNodeC contract2])
listCurryType (ASTNodeC (RedeemCC identCC contract))
 = ("RedeemCC", [ASTNodeCC identCC, ASTNodeC contract])
listCurryType (ASTNodeC (Pay identPay person1 person2 cash timeout contract))
 = ("Pay", [ASTNodeIP identPay, ASTNodeI person1, ASTNodeI person2,
            ASTNodeM cash, ASTNodeI timeout, ASTNodeC contract])
listCurryType (ASTNodeC (Both contract1 contract2))
 = ("Both", [ASTNodeC contract1, ASTNodeC contract2])
listCurryType (ASTNodeC (Choice observation contract1 contract2))
 = ("Choice", [ASTNodeO observation, ASTNodeC contract1, ASTNodeC contract2])
listCurryType (ASTNodeC (When observation timeout contract1 contract2))
 = ("When", [ASTNodeO observation, ASTNodeI timeout, ASTNodeC contract1, ASTNodeC contract2])
listCurryType (ASTNodeCC (IdentCC int)) = ("IdentCC", [ASTNodeI int])
listCurryType (ASTNodeIC (IdentChoice int)) = ("IdentChoice", [ASTNodeI int])
listCurryType (ASTNodeIP (IdentPay int)) = ("IdentPay", [ASTNodeI int])
listCurryType (ASTNodeI int) = (show int, [])

isComplex :: ASTNode -> Bool
isComplex (ASTNodeO _) = True
isComplex (ASTNodeC _) = True
isComplex (ASTNodeM _) = True
isComplex _ = False

--------------------------
-- AST independent code --
--------------------------

data NodeType = Trivial (String, [ASTNode])
              | Simple (String, [ASTNode])
              | Complex (String, [ASTNode])

tabulateLine :: Integer -> String
tabulateLine n = genericReplicate n ' '

classify :: ASTNode -> NodeType
classify x
  | null $ snd r = Trivial r
  | isComplex x = Complex r
  | otherwise = Simple r
  where r = listCurryType x

isTrivial :: NodeType -> Bool
isTrivial (Trivial _) = True
isTrivial _ = False

noneComplex :: NodeType -> NodeType -> Bool
noneComplex (Complex _) _ = False
noneComplex _ (Complex _)= False
noneComplex _ _ = True

-- We assume that Simple nodes have Simple or Trivial children
smartPrettyPrint :: Integer -> NodeType -> String
smartPrettyPrint _ (Trivial a) = prettyPrint 0 a
smartPrettyPrint _ (Simple a) = "(" ++ prettyPrint 0 a ++ ")"
smartPrettyPrint spaces (Complex a) = "(" ++ prettyPrint (spaces + 1) a ++ ")"

prettyPrint :: Integer -> (String, [ASTNode]) -> String
prettyPrint _ (name, []) = name
prettyPrint spaces (name, args) = intercalate "\n" (trivialNames : map (tabulateLine newSpaces ++) others)
  where
    classified = map classify args
    newSpaces = spaces + genericLength name + 1
    groupedClassified = groupBy noneComplex classified
    trivialNames = unwords (name : map (smartPrettyPrint newSpaces) (head groupedClassified))
    others = map (unwords . map (smartPrettyPrint newSpaces)) (tail groupedClassified)

-------------
-- Wrapper --
-------------

prettyPrintContract :: Contract -> String
prettyPrintContract = prettyPrint 0 . listCurryType . ASTNodeC
