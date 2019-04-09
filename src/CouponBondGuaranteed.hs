module CouponBondGuaranteed where

import Semantics
import Data.List (genericLength)

contract :: Contract
contract = couponBondGuaranteed 1 2 3 1000 0.08 50 100 450 30240

couponBondGuaranteed :: Integer -> Integer -> Integer -> Integer -> Double -> Timeout
                     -> Timeout -> Timeout -> Timeout -> Contract
couponBondGuaranteed creatorID counterpartyID guarantor notionalPrincipal nominalInterestRate initialExchangeDate slotCycle maturityDate gracePeriod =
    -- counterpartyID commits a bond face value before initialExchangeDate
    CommitCash (IdentCC 0) counterpartyID (Value notionalPrincipal) initialExchangeDate maturityDate
        -- guarantor commits a 'guarantee' before initialExchangeDate
        (CommitCash (IdentCC 1) guarantor (Value totalPayment) initialExchangeDate (maturityDate + gracePeriod)
            (Both
                -- creatorID can receive the payment from counterpartyID
                (Pay (IdentPay 1) counterpartyID creatorID (Committed (IdentCC 0)) maturityDate Null)
                -- schedule payments
                (Both payments finalPayment)
            )
            -- if no guarantee committed we abort contract and allow to redeem the counterpartyID's commit
            (RedeemCC (IdentCC 0) Null)
        )
        Null
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
    payment amount (ident, paymentDate) =
        -- creatorID commits a coupon payment
        CommitCash (IdentCC ident) creatorID (Value amount) paymentDate (maturityDate + gracePeriod)
            (When FalseObs paymentDate Null
                -- counterpartyID can claim the coupon after payment date
                (Pay (IdentPay ident) creatorID counterpartyID (Committed (IdentCC ident)) (maturityDate + gracePeriod) Null))
            -- in case creatorID did not commit on time the guarantor pays the coupon
            (Pay (IdentPay (ident + 1)) guarantor counterpartyID (Value amount) (maturityDate + gracePeriod) Null)

    -- generate coupon payments for given schedule
    payments = foldr1 Both $ map (payment coupon) idsAndDates
        -- generate IdentCC/IdentPay identifiers for each payment date
        where idsAndDates = zip (map (2*) [1..]) paymentDates

    finalPayment = payment notionalPrincipal (2 * (1 + genericLength paymentDates), maturityDate)
