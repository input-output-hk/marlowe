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

allActions :: [Action i t] -> Timeout -> Contract i t -> Contract i t -> Contract i t
allActions [] _ cont _ = cont
allActions l timeout cont timeoutCont =
  When [Case t $ allActions (b ++ a) timeout cont timeoutCont
        | (b, t, a) <- splitEverywhere l]
       timeout timeoutCont

payAll :: t -> Party i -> Payee i -> Contract i t -> Contract i t
payAll tok acId payee = Pay acId payee tok (AvailableMoney acId tok)

zeroCouponBondGuaranteed :: t -> Party i -> Party i -> Party i -> Integer -> Integer -> Timeout ->
                            Timeout -> Contract i t
zeroCouponBondGuaranteed tok issuer investor guarantor notional discount startDate maturityDate =
   allActions [ Deposit guarantorAcc guarantor tok (Constant notional)
              , Deposit investorAcc investor tok (Constant (notional - discount)) ]
              startDate
              (When []
                    startDate
                    (payAll tok
                            investorAcc (Party issuer)
                            (When [ Case (Deposit investorAcc issuer tok (Constant notional))
                                         Close
                                  ]
                                  maturityDate
                                  (payAll tok
                                          guarantorAcc (Account investorAcc)
                                          Close)
                            )
                    )
              )
              Close
  where guarantorAcc = guarantor
        investorAcc = investor


