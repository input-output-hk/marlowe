
module ZCBG2 where

import Semantics4

zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
  When [ Case (Deposit guarantorAcc guarantor (Constant notional))
              (When [Case (Deposit investorAcc investor (Constant (notional - discount)))
                          continuation]
                    startDate
                    RedeemAll)
       , Case (Deposit investorAcc investor (Constant (notional - discount)))
              (When [Case (Deposit guarantorAcc guarantor (Constant notional))
                          continuation]
                    startDate
                    RedeemAll)
       ]
       startDate
       RedeemAll
  where continuation = When []
                            startDate
                            (Pay investorAcc (Party issuer) (AvailableMoney investorAcc)
                                    (When [ Case (Deposit investorAcc issuer (Constant notional))
                                                 RedeemAll
                                          ]
                                          maturityDate
                                          (Pay guarantorAcc (Account investorAcc) (AvailableMoney guarantorAcc)
                                               RedeemAll)
                                    )
                           )
        guarantorAcc = AccountId 1 guarantor
        investorAcc = AccountId 2 investor


