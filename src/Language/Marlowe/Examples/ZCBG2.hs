
module Language.Marlowe.Examples.ZCBG2 where

import Language.Marlowe


zeroCouponBondGuaranteed :: Party -> Party -> Party -> Integer -> Integer -> Timeout
                         -> Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
  When [ Case (Deposit guarantorAcc guarantor (Constant notional))
              (When [Case (Deposit investorAcc investor (Constant (notional - discount)))
                          continuation]
                    startDate
                    Close)
       , Case (Deposit investorAcc investor (Constant (notional - discount)))
              (When [Case (Deposit guarantorAcc guarantor (Constant notional))
                          continuation]
                    startDate
                    Close)
       ]
       startDate
       Close
  where continuation = When []
                            startDate
                            (Pay investorAcc (Party issuer) (AvailableMoney investorAcc)
                                    (When [ Case (Deposit investorAcc issuer (Constant notional))
                                                 Close
                                          ]
                                          maturityDate
                                          (Pay guarantorAcc (Account investorAcc) (AvailableMoney guarantorAcc)
                                               Close)
                                    )
                           )
        guarantorAcc = AccountId 1 guarantor
        investorAcc = AccountId 2 investor


