module SemanticsProp where

import Semantics
import Interactive
import qualified Data.Map as Map
import Test.QuickCheck.Property
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import qualified Data.Set as Set
import qualified Data.Map as Map


-- WORK IN PROGRESS

-- USING PROPERTY-BASED TESTING TO TEST
-- THE CONTRACTS DSL.


{--------------
 - Generators -
 --------------}

isFailedPay (FailedPay _ _ _) = True 
isFailedPay _ = False

arbitraryCCid :: Gen IdentCC
arbitraryCCid = do x <- choose (1, 10)
                   return $ IdentCC x 

arbitraryCVid :: Gen IdentCV
arbitraryCVid = do x <- choose (1, 10)
                   return $ IdentCV x 

arbitraryCV :: Gen CV
arbitraryCV =  do x <- arbitraryCVid 
                  y <- choose (1, 10)
                  return $ CV x y

arbitraryCC :: Gen CC
arbitraryCC = do x <- arbitraryCCid 
                 y <- choose (1, 10)
                 z <- choose (1, 10)
                 o <- choose (1, 10)
                 return $ CC x y z o 

arbitraryRC :: Gen RC
arbitraryRC =  do x <- arbitraryCCid 
                  y <- choose (1, 10)
                  return $ RC x y

arbitraryRV :: Gen (IdentCV, Value)
arbitraryRV =  do x <- arbitraryCVid 
                  y <- choose (1, 20)
                  return $ (x, y)

arbitrary_observation :: (Eq a, Num a) => a -> Gen Observation
arbitrary_observation s =
  if (s == 0) then elements [ TrueObs, FalseObs ]
  else oneof [ do x <- choose (1, 10)
                  return $ TimeAbove x,
               do o1 <- arbitrary_observation (s - 1)
                  o2 <- arbitrary_observation (s - 1)
                  return $ AndObs o1 o2,
               do o1 <- arbitrary_observation (s - 1)
                  o2 <- arbitrary_observation (s - 1)
                  return $ OrObs o1 o2,
               do o <- arbitrary_observation (s - 1)
                  return $ NotObs o,
               do id <- arbitraryCVid
                  x <- choose (1, 10)
                  return $ CVRevealedAs id x,
               return TrueObs,
               return FalseObs ]


arbitrary_contract_aux :: (Eq a, Num a) => a -> Gen Contract
arbitrary_contract_aux s =
      if (s == 0) then return Null
      else oneof [ return Null,
                    do ccid <- arbitraryCCid
                       sc <- arbitrary_contract_aux (s - 1)
                       return $ RedeemCC ccid sc,
                    do cvid <- arbitraryCVid
                       sc <- arbitrary_contract_aux (s - 1)
                       return $ RevealCV cvid sc,
                    do x <- choose (1, 10)
                       y <- choose (1, 10)
                       z <- choose (1, 20)
                       sc <- arbitrary_contract_aux (s - 1)
                       return $ Pay x y z sc,
                    do sc1 <- arbitrary_contract_aux (s - 1)
                       sc2 <- arbitrary_contract_aux (s - 1)
                       return $ Both sc1 sc2,
                    do sc1 <- arbitrary_contract_aux (s - 1)
                       sc2 <- arbitrary_contract_aux (s - 1)
                       obs <- arbitrary_observation (s - 1)
                       return $ Choice obs sc1 sc2,
                    do CC i p v e <- arbitraryCC
                       sc <- arbitrary_contract_aux (s - 1)
                       return $ CommitCash i p v e sc,
                    do y <- arbitraryCVid 
                       z <- choose (1, 20)
                       sc <- arbitrary_contract_aux (s - 1)
                       vl <- choose (1, 20)
                       return $ CommitValue y z [1..vl] sc
                 ]

arbitrary_commits =
  do cvs <- listOf arbitraryCV
     ccs <- listOf arbitraryCC
     crv <- listOf arbitraryRV
     crc <- listOf arbitraryRC
     return $ Commits (Set.fromList cvs)
                      (Set.fromList ccs)
                      (Map.fromList crv)
                      (Set.fromList crc)

arbitrary_obs =
  do x <- choose (1, 30)
     y <- choose (1, 30)
     z <- choose (1, 30)
     return $ OS x y z

{-----------------------
 - Arbitrary instances -
 -----------------------}

instance Arbitrary Contract where
  arbitrary = (sized (\s -> arbitrary_contract_aux s))

instance Arbitrary Commits where
  arbitrary = arbitrary_commits

instance Arbitrary OS where
  arbitrary = arbitrary_obs

instance Arbitrary Observation where
  arbitrary = (sized (\s -> arbitrary_observation s))

{--------------
 - Properties -
 --------------}

-- Is there any circumstance in which a FailedPay is emitted?
valid com con obs = ((filter (isFailedPay) nas) == [])
  where (ns, ncon, nas) = (compute_all com (Map.empty, Map.empty) con obs)

-- Is there any circumstance in which a contract is not reduced?
reduces com con obs = (ncon == Null)
  where (ns, ncon, nas) = (compute_all com (Map.empty, Map.empty) con obs)


