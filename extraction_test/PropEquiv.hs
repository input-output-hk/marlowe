module PropEquiv where

import qualified Semantics as HS
import qualified SemanticsCoq as CS
import qualified Data.Map as M
import qualified Data.Set as S
import GenSemantics
import Test.QuickCheck

convertMoney :: HS.Money -> CS.Money
convertMoney (HS.AvailableMoney (HS.IdentCC ident)) = (CS.AvailableMoney ident)
convertMoney (HS.AddMoney m1 m2) = (CS.AddMoney (convertMoney m1) (convertMoney m2))
convertMoney (HS.ConstMoney c) = (CS.ConstMoney c)
convertMoney (HS.MoneyFromChoice (HS.IdentChoice ident) p m) = (CS.MoneyFromChoice ident p (convertMoney m))

convertObservation :: HS.Observation -> CS.Observation
convertObservation (HS.BelowTimeout t) = (CS.BelowTimeout t)
convertObservation (HS.AndObs o1 o2) = (CS.AndObs (convertObservation o1) (convertObservation o2))
convertObservation (HS.OrObs o1 o2) = (CS.OrObs (convertObservation o1) (convertObservation o2))
convertObservation (HS.NotObs o) = (CS.NotObs (convertObservation o))
convertObservation (HS.PersonChoseThis (HS.IdentChoice ident) p c) = (CS.PersonChoseThis ident p c)
convertObservation (HS.PersonChoseSomething (HS.IdentChoice ident) p) = (CS.PersonChoseSomething ident p)
convertObservation (HS.ValueGE m1 m2) = (CS.ValueGE (convertMoney m1) (convertMoney m2))
convertObservation (HS.TrueObs) = (CS.TrueObs)
convertObservation (HS.FalseObs) = (CS.FalseObs)

convertContract :: HS.Contract -> CS.Contract
convertContract (HS.Null) = (CS.Null)
convertContract (HS.CommitCash (HS.IdentCC ident) p m t1 t2 c1 c2) = (CS.CommitCash ident p (convertMoney m) t1 t2 (convertContract c1) (convertContract c2))
convertContract (HS.RedeemCC (HS.IdentCC ident) c) = (CS.RedeemCC ident (convertContract c))
convertContract (HS.Pay (HS.IdentPay ident) p1 p2 m t c) = (CS.Pay ident p1 p2 (convertMoney m) t (convertContract c))
convertContract (HS.Both c1 c2) = (CS.Both (convertContract c1) (convertContract c2))
convertContract (HS.Choice o c1 c2) = (CS.Choice (convertObservation o) (convertContract c1) (convertContract c2))
convertContract (HS.When o t c1 c2) = (CS.When (convertObservation o) t (convertContract c1) (convertContract c2))

convertInput :: HS.Input -> CS.InputT
convertInput (HS.Input w x y z) = (CS.composeInput (map convertCC $ S.toList w)
                                                   (map convertRC $ S.toList x)
                                                   (map convertRP $ M.toList y)
                                                   (map convertIC $ M.toList z))
  where 
    convertCC (HS.CC (HS.IdentCC a) b c d) = (CS.CC a b c d)
    convertRC (HS.RC (HS.IdentCC a) b c) = (CS.RC a b c)
    convertRP ((HS.IdentPay a, b), c) = ((a, b), c)
    convertIC ((HS.IdentChoice a, b), c) = ((a, b), c)

convertAction :: HS.Action -> CS.Action
convertAction (HS.SuccessfulPay (HS.IdentPay ident) p1 p2 c) = (CS.SuccessfulPay ident p1 p2 c)
convertAction (HS.ExpiredPay (HS.IdentPay ident) p1 p2 c) = (CS.ExpiredPay ident p1 p2 c)
convertAction (HS.FailedPay (HS.IdentPay ident) p1 p2 c) = (CS.FailedPay ident p1 p2 c)
convertAction (HS.SuccessfulCommit (HS.IdentCC ident) p c e) = (CS.SuccessfulCommit ident p c e)
convertAction (HS.CommitRedeemed (HS.IdentCC ident) p c) = (CS.CommitRedeemed ident p c)
convertAction (HS.ExpiredCommitRedeemed (HS.IdentCC ident) p c) = (CS.ExpiredCommitRedeemed ident p c)
convertAction (HS.DuplicateRedeem (HS.IdentCC ident) p) = (CS.DuplicateRedeem ident p)
convertAction (HS.ChoiceMade (HS.IdentChoice ident) p c) = (CS.ChoiceMade ident p c)

prop_equivalent_step :: Property
prop_equivalent_step = forAll ((\x y z -> (x, y, z)) <$> arbitraryContract <*> arbitraryInput <*> arbitrary)
    (\(contr, inp, bn) -> let (ns1, nc1, nas1) = HS.step inp HS.emptyState contr (HS.OS bn bn) in
                          let (ns2, nc2, nas2) = CS.stepWrap (convertInput inp) CS.emptyState (convertContract contr) bn in
                          whenFail (do {putStrLn ""; putStrLn "Results:";
                                        putStrLn (show (convertContract nc1));
                                        putStrLn (show nc2);
                                        putStrLn "";
                                        putStrLn (show (map convertAction nas1));
                                        putStrLn (show nas2); putStrLn ""}) ((convertContract nc1 == nc2) && ((map (convertAction) nas1) == nas2)))

 
are_equivalent :: (HS.Contract, HS.Input, HS.BlockNumber) -> Property
are_equivalent (contr, inp, bn) =
                          whenFail (do {putStrLn ""; putStrLn "Results:";
                                        putStrLn (show (convertContract nc1));
                                        putStrLn (show nc2);
                                        putStrLn "";
                                        putStrLn (show (map convertAction nas1));
                                        putStrLn (show nas2); putStrLn ""}) ((convertContract nc1 == nc2) && ((map (convertAction) nas1) == nas2))
  where (ns1, nc1, nas1) = HS.stepBlock inp HS.emptyState contr (HS.OS bn bn)
        (ns2, nc2, nas2) = CS.stepBlockWrap (convertInput inp) CS.emptyState (convertContract contr) bn

prop_equivalent :: Property
prop_equivalent = forAll ((\x y z -> (x, y, z)) <$> arbitraryContract <*> arbitraryInput <*> arbitrary) are_equivalent

are_equivalent_full :: (HS.Contract, [HS.Input]) -> Property
are_equivalent_full (contr, inp) =
                          whenFail (do {putStrLn ""; putStrLn "Results:";
                                        putStrLn (show (convertContract nc1));
                                        putStrLn (show nc2);
                                        putStrLn "";
                                        putStrLn (show (map convertAction nas1));
                                        putStrLn (show nas2); putStrLn ""}) ((convertContract nc1 == nc2) && ((map (convertAction) nas1) == nas2))
  where (ns1, nc1, _, nas1) = HS.executeConcreteTrace contr inp
        (ns2, nc2, _, nas2) = CS.executeConcreteTraceWrap (convertContract contr) (map convertInput inp)

prop_equivalent_full :: Property
prop_equivalent_full = forAll ((\x y -> (x, y)) <$> arbitraryContract <*> listOf arbitraryInput) are_equivalent_full
 
