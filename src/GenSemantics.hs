module GenSemantics where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Semantics
import Test.QuickCheck

boundedValue :: Set Person -> Set IdentCC -> Bounds -> Gen Value
boundedValue participants commits bounds = sized $ boundedValueAux participants commits bounds

boundedValueAux :: Set Person -> Set IdentCC -> Bounds -> Int -> Gen Value
boundedValueAux participants commits bounds s = do
    let committed = S.toList commits
    let parties   = S.toList participants
    let choices   = M.keys $ choiceBounds bounds
    let oracles   = M.keys $ oracleBounds bounds
    let go        = boundedValueAux participants commits bounds
    case compare s 0 of
        GT -> oneof [ Committed <$> elements committed
                    , (AddValue <$> go 0) <*> go (s - 1)
                    , (MulValue <$> go 0) <*> go (s - 1)
                    , (DivValue <$> go 0) <*> go (s - 1)
                    , Value <$> positiveAmount
                    , ValueFromChoice <$> elements choices <*> elements parties <*> go (s - 1)
                    , ValueFromOracle <$> elements oracles <*> go (s - 1) ]
        EQ -> oneof [ Committed <$> elements committed
                    , Value <$> positiveAmount ]
        LT -> error "Negative size in arbitraryValue"


positiveAmount :: Gen Integer
positiveAmount = fmap abs arbitrary

arbitraryValueAux :: Int -> Gen Value
arbitraryValueAux s
 | s > 0 = oneof [ Committed . IdentCC <$> arbitrary
                 , (AddValue <$> arbitraryValueAux (s - 1)) <*> arbitraryValueAux (s - 1)
                 , (MulValue <$> arbitraryValueAux (s - 1)) <*> arbitraryValueAux (s - 1)
                --  , (DivValue <$> arbitraryValueAux (s - 1)) <*> arbitraryValueAux (s - 1)
                 , Value <$> positiveAmount
                 , ValueFromChoice . IdentChoice <$> arbitrary <*> arbitrary <*> arbitraryValueAux (s - 1) ]
 | s == 0 = oneof [ Committed . IdentCC <$> arbitrary
                  , Value <$> positiveAmount ]
 | otherwise = error "Negative size in arbitraryValue"

arbitraryValue :: Gen Value
arbitraryValue = sized arbitraryValueAux

arbitraryObservationAux :: Int -> Gen Observation
arbitraryObservationAux s
 | s > 0 = oneof [BelowTimeout <$> arbitrary
                 ,AndObs <$> arbitraryObservationAux (s - 1) <*> arbitraryObservationAux (s - 1)
                 ,OrObs <$> arbitraryObservationAux (s - 1) <*> arbitraryObservationAux (s - 1)
                 ,NotObs <$> arbitraryObservationAux (s - 1)
                 ,(PersonChoseThis . IdentChoice) <$> arbitrary <*> arbitrary <*>  arbitrary
                 ,(PersonChoseSomething . IdentChoice) <$> arbitrary <*> arbitrary
                 ,ValueGE <$> arbitraryValueAux (s - 1) <*> arbitraryValueAux (s - 1)
                 ,pure TrueObs,pure FalseObs]
 | s == 0 = oneof [BelowTimeout <$> arbitrary
                  ,(PersonChoseThis . IdentChoice) <$> arbitrary <*> arbitrary <*>  arbitrary
                  ,(PersonChoseSomething . IdentChoice) <$> arbitrary <*> arbitrary
                  ,pure TrueObs,pure FalseObs]
 | otherwise = error "Negative size in arbitraryObservation"


arbitraryObservation :: Gen Observation
arbitraryObservation = sized arbitraryObservationAux

arbitraryContractAux :: Int -> Gen Contract
arbitraryContractAux s
 | s > 0 = oneof [pure Null
                 ,(CommitCash . IdentCC) <$> arbitrary <*> arbitrary <*> arbitraryValueAux (s - 1) <*> arbitrary <*> arbitrary <*> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1)
                 ,(RedeemCC . IdentCC) <$> arbitrary <*> arbitraryContractAux (s - 1)
                 ,(Pay . IdentPay) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitraryValueAux (s - 1) <*> arbitrary <*> arbitraryContractAux (s - 1)
                 ,Both <$> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1)
                 ,Choice <$> arbitraryObservationAux (s - 1) <*> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1)
                 ,When <$> arbitraryObservationAux (s - 1) <*> arbitrary <*> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1)]
 | s == 0 = oneof [pure Null]
 | otherwise = error "Negative size in arbitraryObservation"

arbitraryContract :: Gen Contract
arbitraryContract = sized arbitraryContractAux

arbitraryCC :: Gen CC
arbitraryCC = (CC . IdentCC) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

arbitraryRC :: Gen RC
arbitraryRC = (RC . IdentCC) <$> arbitrary <*> arbitrary <*> arbitrary

arbitraryRPEntry :: Gen ((IdentPay, Person), Cash)
arbitraryRPEntry = (\x y z -> ((IdentPay x, y), z)) <$> arbitrary <*> arbitrary <*> arbitrary

arbitraryICEntry :: Gen ((IdentChoice, Person), ConcreteChoice)
arbitraryICEntry = (\x y z -> ((IdentChoice x, y), z)) <$> arbitrary <*> arbitrary <*> arbitrary

arbitraryInputAux :: Int -> Gen Input
arbitraryInputAux s = (\w x y z -> Input (S.fromList w) (S.fromList x) (M.fromList y) (M.fromList z))
                      <$> vectorOf s arbitraryCC <*> vectorOf s arbitraryRC <*> vectorOf s arbitraryRPEntry <*> vectorOf s arbitraryICEntry

arbitraryInput :: Gen Input
arbitraryInput = sized arbitraryInputAux
