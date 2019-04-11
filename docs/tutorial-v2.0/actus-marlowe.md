# ACTUS and Marlowe

This tutorial gives an introduction to the general idea of the ACTUS standards for the algorithmic representation of financial contracts, plus examples implemented in Marlowe.

## ACTUS

The ACTUS Financial Research Foundation [https://www.actusfrf.org](https://www.actusfrf.org) has created a standard for financial contracts, categorised by means of a [taxonomy](https://www.actusfrf.org/taxonomy) and described in a detailed [technical specification](https://www.actusfrf.org/algorithmic-standard).

The ACTUS standards build on the understanding that financial contracts are legal agreements between two
(or more) counterparties on the exchange of future cash flows. Historically, such legal agreements are described in natural language leading to ambiguity and artificial diversity. As a response, the ACTUS standards define financial contracts by means of a set of contractual terms and deterministic functions mapping these terms onto future payment obligations. Thereby, it is possible to describe the vast majority of financial instruments through a set of little more than 30 Contract Types or modular templates, respectively.

The ACTUS specifications provide a breadth of exercises for implementation in Marlowe, and we illustrate an approach to this in the following example.

## Simple Safe Zero Coupon Bond Example

A zero-coupon bond is a debt security that doesn't pay interest (a coupon)
but is traded at a deep discount, rendering profit at maturity
when the bond is redeemed for its full face value.

For example, an investor can buy a bond that costs 1000 Ada with 8% discount.
He pays 920 Ada to the bond issuer before _start date_.

Later, after _maturity date_, investor can exchange the bond for its full notional, i.e. 1000 Ada.

```haskell
zeroCouponBond :: Person -> Person -> Integer -> Integer -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBond creatorID counterpartyID notionalPrincipal premiumDiscount initialExchangeDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    Commit 1 1 counterpartyID (Constant (notionalPrincipal - premiumDiscount)) initialExchangeDate maturityDate
        -- issuer must commit a full notional value of a bond
        (Commit 2 2 creatorID (Constant notionalPrincipal) initialExchangeDate (maturityDate + gracePeriod)
            (When FalseObs initialExchangeDate Null
                -- after start date but before maturity date the issuer can receive the bond payment
                (Pay 3 1 creatorID (Committed 1) maturityDate
                    (When FalseObs maturityDate Null
                        -- after maturity date the investor can claim bond's full value
                        (Pay 4 2 counterpartyID (Committed 2)
                            (maturityDate + gracePeriod) Null Null)
                    )
                    Null
                )
            )
            Null
        )
        Null
````

This contract has a significant drawback requiring the issuer to commit the full bond notional value before _start date_, making the contract arguably useless.

There are at least two ways to solve this: we could trust our issuer and do not require him to commit beforehand, or we could ask a third party to be a guarantor of the deal. 

> __Exercises__
>
> Give a variant of the `zeroCouponBond` contract in which it is not necessary for the bond creator to put the full payment up before the bond is issued.
>
> Give a variant of the `zeroCouponBond` contract which also includes a `guarantor` who puts up the full payment up before the bond is issued, and who will pay that counterparty if the issuer defaults; if the issuer does make the payment in time, then the guarantor should recover their money. 

## Guaranteed Coupon Bond Example

This more complex bond involves a guarantor who puts up the notional principal value at the start of the contract. Repayments are calculated according to a schedule of every `slotCycle` slots until `maturityDate`. At each payment slot, the guarantor pays if (and only if) the issuer does not.

```haskell
couponBondGuaranteed :: Integer -> Integer -> Integer -> Integer -> Double
                     -> Timeout -> Timeout -> Timeout -> Timeout -> Contract
couponBondGuaranteed creatorID counterpartyID guarantor notionalPrincipal
                     nominalInterestRate initialExchangeDate slotCycle
                     maturityDate gracePeriod =
    -- counterpartyID commits a bond face value before initialExchangeDate
    Commit 1 0 counterpartyID (Constant notionalPrincipal) initialExchangeDate maturityDate
        -- guarantor commits a 'guarantee' before initialExchangeDate
        (Commit 2 1 guarantor (Constant totalPayment) initialExchangeDate (maturityDate + gracePeriod)
            (Both
                -- creatorID can receive the payment from counterpartyID
                (Pay 4 1 creatorID (Committed 0) maturityDate Null Null)
                -- schedule payments
                (Both payments finalPayment)
            )
            -- if no guarantee committed we abort contract and allow to redeem the counterpartyID's commit
            (Pay 3 0 counterpartyID (Committed 0) maturityDate Null Null)
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
        Commit baseActionId ident creatorID (Constant amount) paymentDate (maturityDate + gracePeriod)
            (When FalseObs paymentDate Null
                -- counterpartyID can claim the coupon after payment date
                (Pay (baseActionId + 1) ident counterpartyID (Committed ident) (maturityDate + gracePeriod) Null Null))
            -- in case creatorID did not commit on time the guarantor pays the coupon
            (Pay (baseActionId + 2) (ident + 1) counterpartyID (Constant amount) (maturityDate + gracePeriod) Null Null)
        where baseActionId = (5 + ((ident `div` 2) - 1) * 3)

    -- generate coupon payments for given schedule
    payments = foldr1 Both $ map (payment coupon) idsAndDates
        -- generate IdentCC/IdentPay identifiers for each payment date
        where idsAndDates = zip (map (2*) [1..]) paymentDates

    finalPayment = payment notionalPrincipal (2 * (1 + genericLength paymentDates), maturityDate)
```

IOHK plans to implement the full ACTUS standard using Marlowe and Plutus over the coming year.

### [Prev](./meadow-overview.md) [Up](./README.md) [Next](./marlowe-plutus.md)
