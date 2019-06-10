module CouponBondGuaranteed where

import Minimal
import Data.List (genericLength)

contract :: Contract
contract = couponBondGuaranteed 1 2 3 1000 0.08 5 10 45

couponBondGuaranteed :: Integer -> Integer -> Integer -> Integer -> Double
                     -> Timeout -> Timeout -> Timeout -> Contract
couponBondGuaranteed creatorID counterpartyID guarantor notionalPrincipal
                     nominalInterestRate initialExchangeDate slotCycle
                     maturityDate =
  When [Case (AndObs (ValueEQ (CommittedBy counterpartyID) (Constant notionalPrincipal))
                     (ValueEQ (CommittedBy guarantor) (Constant totalPayment)))
             (When []
                   initialExchangeDate
                   (Pay [((Constant notionalPrincipal), creatorID)]
                        (Right (payments finalPayment))))]
       initialExchangeDate -- if money is not provided by initialExchangeDate we return all the money
       (Pay [(CommittedBy p, p) | p <- [creatorID, counterpartyID]]
            (Left guarantor))
  where
    cycles = takeWhile (\i ->
            let paymentDate = initialExchangeDate + i * slotCycle
            in paymentDate < maturityDate
        ) [1..]

    -- calculate payment schedule
    paymentDates = map (\i -> initialExchangeDate + i * slotCycle) cycles

    coupon = round $ fromIntegral notionalPrincipal * nominalInterestRate

    -- calculate total amount of payments to be ensured by guarantor
    totalPayment = notionalPrincipal + coupon * genericLength cycles

    -- generate Commit/Pay for each scheduled payment
    payment amount paymentDate cont =
        (When []
              paymentDate
              (Pay [(Constant amount, counterpartyID)]
                   (Right cont)))

    -- generate coupon payments for given schedule
    payments = foldr1 (.) $ map (payment coupon) paymentDates 

    finalPayment = (Pay [(Constant notionalPrincipal, counterpartyID) -- we pay counterparty back
                        -- OPTIONAL: return excess to counterparty
                        ,(SubValue (CommittedBy counterpartyID) (Constant notionalPrincipal), counterpartyID)
                        -- OPTIONAL: return excess to creator
                        ,(SubValue (CommittedBy creatorID) (Constant totalPayment), creatorID)]
                        (Left guarantor)) -- whatever is left goes back to the guarantor
 

couponBondGuaranteedExpanded =
  When [Case (AndObs (ValueEQ (CommittedBy 2) (Constant 1000))
                     (ValueEQ (CommittedBy 3) (Constant 1240)))
             (When [] 5
               (Pay [(Constant 1000,1)]
                    (Right (When [] 15
                              (Pay [(Constant 80,2)]
                                   (Right (When [] 25
                                             (Pay [(Constant 80,2)]
                                                  (Right (When [] 35
                                                     (Pay [(Constant 80,2)]
                                                          (Right (Pay [(Constant 1000,2)
                                                                      ,(SubValue (CommittedBy 2) (Constant 1000),2)
                                                                      ,(SubValue (CommittedBy 1) (Constant 1240),1)]
                                                                      (Left 3))))))))))))))]
       5 (Pay [(CommittedBy 1,1),(CommittedBy 2,2)] (Left 3))


