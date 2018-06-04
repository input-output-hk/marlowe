module GenSemantics where

import Semantics
import Test.QuickCheck

arbitraryMoneyAux :: Int -> Gen Money
arbitraryMoneyAux s
 | s > 0 = oneof [(AvailableMoney . IdentCC) <$> arbitrary
                 ,(AddMoney <$> arbitraryMoneyAux (s - 1)) <*> arbitraryMoneyAux (s - 1)
                 ,ConstMoney <$> arbitrary
                 ,(MoneyFromChoice . IdentChoice) <$> arbitrary <*> arbitrary <*> arbitraryMoneyAux (s - 1)]
 | s == 0 = oneof [(AvailableMoney . IdentCC) <$> arbitrary
                  ,ConstMoney <$> arbitrary]
 
arbitraryMoney :: Gen Money
arbitraryMoney = sized arbitraryMoneyAux

arbitraryObservationAux :: Int -> Gen Observation
arbitraryObservationAux s
 | s > 0 = oneof [BelowTimeout <$> arbitrary
                 ,AndObs <$> arbitraryObservationAux (s - 1) <*> arbitraryObservationAux (s - 1) 
                 ,OrObs <$> arbitraryObservationAux (s - 1) <*> arbitraryObservationAux (s - 1)
                 ,NotObs <$> arbitraryObservationAux (s - 1)  
                 ,(PersonChoseThis . IdentChoice) <$> arbitrary <*> arbitrary <*>  arbitrary
                 ,(PersonChoseSomething . IdentChoice) <$> arbitrary <*> arbitrary
                 ,ValueGE <$> arbitraryMoneyAux (s - 1) <*> arbitraryMoneyAux (s - 1)
                 ,pure TrueObs,pure FalseObs]
 | s == 0 = oneof [BelowTimeout <$> arbitrary
                  ,(PersonChoseThis . IdentChoice) <$> arbitrary <*> arbitrary <*>  arbitrary
                  ,(PersonChoseSomething . IdentChoice) <$> arbitrary <*> arbitrary
                  ,pure TrueObs,pure FalseObs]


arbitraryObservation :: Gen Observation
arbitraryObservation = sized arbitraryObservationAux


