
module ZCBG2 where

import Semantics4


zeroCouponBondGuaranteed :: Party -> Party -> Party -> Integer -> Integer -> Timeout
                         -> Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
  When [ Case (Deposit guarantorAcc guarantor (Constant notional))
              (When [Case (Deposit investorAcc investor (Constant (notional - discount)))
                          continuation]
                    startDate
                    Refund)
       , Case (Deposit investorAcc investor (Constant (notional - discount)))
              (When [Case (Deposit guarantorAcc guarantor (Constant notional))
                          continuation]
                    startDate
                    Refund)
       ]
       startDate
       Refund
  where continuation = When []
                            startDate
                            (Pay investorAcc (Party issuer) (AvailableMoney investorAcc)
                                    (When [ Case (Deposit investorAcc issuer (Constant notional))
                                                 Refund
                                          ]
                                          maturityDate
                                          (Pay guarantorAcc (Account investorAcc) (AvailableMoney guarantorAcc)
                                               Refund)
                                    )
                           )
        guarantorAcc = AccountId 1 guarantor
        investorAcc = AccountId 2 investor


