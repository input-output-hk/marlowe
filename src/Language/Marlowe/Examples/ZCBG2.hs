
module Language.Marlowe.Examples.ZCBG2 where

import Language.Marlowe


zeroCouponBondGuaranteed :: Party -> Party -> Party -> Integer -> Integer -> Timeout
                         -> Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
  When [ Case (Deposit guarantorAcc guarantor ada (Constant notional))
              (When [Case (Deposit investorAcc investor ada (Constant (notional - discount)))
                          continuation]
                    startDate
                    Close)
       , Case (Deposit investorAcc investor ada (Constant (notional - discount)))
              (When [Case (Deposit guarantorAcc guarantor ada (Constant notional))
                          continuation]
                    startDate
                    Close)
       ]
       startDate
       Close
  where continuation = When []
                            startDate
                            (Pay investorAcc (Party issuer) ada (AvailableMoney investorAcc ada)
                                    (When [ Case (Deposit investorAcc issuer ada (Constant notional))
                                                 Close
                                          ]
                                          maturityDate
                                          (Pay guarantorAcc (Account investorAcc) ada (AvailableMoney guarantorAcc ada)
                                               Close)
                                    )
                           )
        guarantorAcc = guarantor
        investorAcc = investor


