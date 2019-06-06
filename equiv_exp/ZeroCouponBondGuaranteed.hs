module ZeroCouponBondGuaranteed where

import Minimal

zeroCouponBondGuaranteed :: Party -> Party -> Party -> Integer -> Integer -> Timeout -> Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
  When [Case (AndObs (ValueEQ (CommittedBy investor) (Constant (notional - discount)))
                     (ValueEQ (CommittedBy guarantor) (Constant notional))) -- Wait for investor and guarantor to commit
             (When []
                   startDate
                   (Pay [(Constant (notional - discount), issuer)] -- We give issuer the discounted amount
                        (Right (When []
                                     maturityDate  -- by maturity date
                                     (Pay [(Constant notional, investor) -- we pay the investor back
                                          -- OPTIONAL: return excess to issuer
                                          ,(SubValue (CommittedBy issuer) (Constant notional), issuer)
                                          -- OPTIONAL: return excess too investor
                                          ,(SubValue (CommittedBy investor) (Constant (notional - discount)), investor)]
                                          (Left guarantor)))))) -- whatever is left goes back to the guarantor
       ]
       startDate -- if money is not provided by startDate we return all the money
       (Pay [(CommittedBy p, p) | p <- [investor, issuer]]
            (Left guarantor))
