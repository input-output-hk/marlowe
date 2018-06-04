module PropAnalysis where

import Semantics
import Analysis
import GenSemantics
import Test.QuickCheck

prop_observationSatisfied = forAll arbitraryObservation
    (\obs -> let res = satisfyObservation obs in
             if (res /= Nothing)
             then (case res of
                     Just (st, os) -> interpretObs st obs os
                     Nothing -> False)
             else (case satisfyObservation (NotObs obs) of
                     Just (st, os) -> not $ interpretObs st obs os
                     Nothing -> False))

