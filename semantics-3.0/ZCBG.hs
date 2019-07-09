module ZCBG where

import Semantics4
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

payAll :: AccountId -> Payee -> Contract -> Contract
payAll acId payee cont =
  Pay acId payee (AvailableMoney acId) cont

zeroCouponBondGuaranteed :: Party -> Party -> Party -> Integer -> Integer -> Timeout ->
                            Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate =
   allActions [ Deposit guarantorAcc guarantor (Constant notional)
              , Deposit investorAcc investor (Constant (notional - discount)) ]
              startDate
              (When []
                    startDate
                    (payAll investorAcc (Party issuer)
                            (When [ Case (Deposit investorAcc issuer (Constant notional))
                                         RedeemAll
                                  ]
                                  maturityDate
                                  (payAll guarantorAcc (Account investorAcc)
                                          RedeemAll)
                            )
                    )
              )
              RedeemAll
  where guarantorAcc = AccountId 1 guarantor
        investorAcc = AccountId 2 investor


