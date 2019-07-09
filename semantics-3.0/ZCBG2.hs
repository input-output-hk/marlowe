
module ZCBG2 where

import Semantics4

zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
  When [ Case (Deposit guarantorAcc guarantor (Constant (notional - discount)))
              (When [Case (Deposit investorAcc investor (Constant notional))
                          continuation]
                    startDate
                    RedeemAll)
       , Case (Deposit investorAcc investor (Constant notional))
              (When [Case (Deposit guarantorAcc guarantor (Constant (notional - discount)))
                          continuation]
                    startDate
                    RedeemAll)
       ]
       startDate
       RedeemAll
  where continuation = (When [] startDate (Pay guarantorAcc
                                               (Party issuer)
                                               (AvailableMoney investorAcc)
                                               (When [Case (Deposit guarantorAcc 
                                                                    issuer
                                                                    (Constant notional))
                                                           RedeemAll]
                                                     maturityDate
                                                     RedeemAll)))
        guarantorAcc = AccountId 1 guarantor
        investorAcc = AccountId 2 investor



