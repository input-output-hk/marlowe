
module Language.Marlowe.Examples.ZCBG2 where

import Language.Marlowe


zeroCouponBondGuaranteed :: t -> Party i -> Party i -> Party i -> Integer -> Integer -> Timeout
                         -> Timeout -> Contract i t
zeroCouponBondGuaranteed tok issuer investor guarantor notional discount startDate maturityDate =
  When [ Case (Deposit guarantorAcc guarantor tok (Constant notional))
              (When [Case (Deposit investorAcc investor tok (Constant (notional - discount)))
                          continuation]
                    startDate
                    Close)
       , Case (Deposit investorAcc investor tok (Constant (notional - discount)))
              (When [Case (Deposit guarantorAcc guarantor tok (Constant notional))
                          continuation]
                    startDate
                    Close)
       ]
       startDate
       Close
  where continuation = When []
                            startDate
                            (Pay investorAcc (Party issuer) tok (AvailableMoney investorAcc tok)
                                    (When [ Case (Deposit investorAcc issuer tok (Constant notional))
                                                 Close
                                          ]
                                          maturityDate
                                          (Pay guarantorAcc (Account investorAcc) tok (AvailableMoney guarantorAcc tok)
                                               Close)
                                    )
                           )
        guarantorAcc = guarantor
        investorAcc = investor


