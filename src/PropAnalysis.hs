module PropAnalysis where

import Semantics
import Analysis
import GenSemantics
import Test.QuickCheck

prop_observationSatisfied = forAll arbitraryObservation
    (\obs -> let res = satisfyObservation obs in
             res /= Nothing ==> case res of
                                  Just (st, os) -> interpretObs st obs os
                                  Nothing -> False)

