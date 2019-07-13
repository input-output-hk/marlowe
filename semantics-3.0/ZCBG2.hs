
module ZCBG2 where

import Semantics4

zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
  When [ Case (Deposit guarantorAcc guarantor (Constant notional))
              (When [Case (Deposit investorAcc investor (Constant (notional - discount)))
                          continuation]
                    startDate
                    RefundAll)
       , Case (Deposit investorAcc investor (Constant (notional - discount)))
              (When [Case (Deposit guarantorAcc guarantor (Constant notional))
                          continuation]
                    startDate
                    RefundAll)
       ]
       startDate
       RefundAll
  where continuation = When []
                            startDate
                            (Pay investorAcc (Party issuer) (AvailableMoney investorAcc)
                                    (When [ Case (Deposit investorAcc issuer (Constant notional))
                                                 RefundAll
                                          ]
                                          maturityDate
                                          (Pay guarantorAcc (Account investorAcc) (AvailableMoney guarantorAcc)
                                               RefundAll)
                                    )
                           )
        guarantorAcc = AccountId 1 guarantor
        investorAcc = AccountId 2 investor


