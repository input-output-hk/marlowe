module Language.Marlowe.Examples.ZCBG where

import Language.Marlowe
import Data.List (inits, tails)

splitEverywhere :: [a] -> [([a], a, [a])]
splitEverywhere xs =
   map
      (\(y, zs0) ->
         case zs0 of
            z:zs -> (y,z,zs)
            [] -> error "splitEverywhere: empty list")
      (init (zip (inits xs) (tails xs)))

allActions :: [Action] -> Timeout -> Contract -> Contract -> Contract
allActions [] _ cont _ = cont
allActions l timeout cont timeoutCont =
  When [Case t $ allActions (b ++ a) timeout cont timeoutCont
        | (b, t, a) <- splitEverywhere l]
       timeout timeoutCont

payAll :: Party -> Payee -> Contract -> Contract
payAll acId payee = Pay acId payee ada (AvailableMoney acId ada)

zeroCouponBondGuaranteed :: Party -> Party -> Party -> Integer -> Integer -> Timeout ->
                            Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
   allActions [ Deposit guarantorAcc guarantor ada(Constant notional)
              , Deposit investorAcc investor ada (Constant (notional - discount)) ]
              startDate
              (When []
                    startDate
                    (payAll investorAcc (Party issuer)
                            (When [ Case (Deposit investorAcc issuer ada (Constant notional))
                                         Close
                                  ]
                                  maturityDate
                                  (payAll guarantorAcc (Account investorAcc)
                                          Close)
                            )
                    )
              )
              Close
  where guarantorAcc = guarantor
        investorAcc = investor


