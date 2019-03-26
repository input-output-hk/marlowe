# ACTUS and Marlowe

This tutorial gives an introduction to the general idea of the ACTUS standards for the algorithmic representation of financial contracts, plus examples implemented in Marlowe (at least the PAM contract, and hopefully others).

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
zeroCouponBond :: PubKey -> PubKey -> Int -> Int -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBond issuer investor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    CommitCash (IdentCC 1) investor (Value (notional - discount)) startDate maturityDate
        -- issuer must commit a full notional value of a bond
        (CommitCash (IdentCC 2) issuer (Value notional) startDate (maturityDate + gracePeriod)
            (When FalseObs startDate Null
                -- after start date but before maturity date the issuer can receive the bond payment
                (Pay (IdentPay 1) investor issuer (Committed (IdentCC 1)) maturityDate
                    (When FalseObs maturityDate Null
                        -- after maturity date the investor can claim bond's full value
                        (Pay (IdentPay 2) issuer investor (Committed (IdentCC 2))
                            (maturityDate + gracePeriod) Null)
                    )
                )
            )
            Null
        )
        Null
```

This contract has a significant drawback requiring the issuer to commit the full bond notional value
before _start date_, making the contract arguably useless.

There are at least two ways to solve this: we could trust our issuer and do not require him to commit beforehand,
or we could ask a third party to be a guarantor of the deal. We'll show both solutions.

## Trusted Zero Coupon Bond Example

The _issuer_ is not forced to commit before _start date_, hence it's a trusted bond,
as the final payment can fail. If an _investor_ does not redeem the bond value during
_grace period_ after _maturity date_ the _issuer_ can keep the value.

```haskell
trustedZeroCouponBond :: PubKey -> PubKey -> Int -> Int -> Timeout -> Timeout -> Timeout -> Contract
trustedZeroCouponBond issuer investor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    -- if the issuer won't pull the payment, investor can redeem the commit after maturityDate
    CommitCash (IdentCC 1) investor (Value (notional - discount)) startDate maturityDate
        (When FalseObs startDate Null -- after startDate
            -- issuer can 'pull' the payment before maturityDate
            (Pay (IdentPay 1) investor issuer (Committed (IdentCC 1)) maturityDate
                -- issuer must commit a bond value before maturityDate
                -- issuer can redeem committed value if the inverstor won't 'pull' the payment
                -- within gracePeriod after maturityDate
                (CommitCash (IdentCC 2) issuer (Value notional) maturityDate (maturityDate + gracePeriod)
                    (When FalseObs maturityDate Null
                        (Pay (IdentPay 2) issuer investor (Committed (IdentCC 2))
                            (maturityDate + gracePeriod) Null))
                    Null
                )
            )
        )
        Null
```

## Zero Coupon Bond with Guarantor Example

Zero coupon bond with _guarantor_ party, who secures _issuer_ payment with _guarantee_.

```haskell
zeroCouponBondGuaranteed :: PubKey -> PubKey -> PubKey -> Int -> Int -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    CommitCash (IdentCC 1) investor (Value (notional - discount)) startDate maturityDate
        -- guarantor commits a 'guarantee' before startDate
        (CommitCash (IdentCC 2) guarantor (Value notional) startDate (maturityDate + gracePeriod)
            (When FalseObs startDate Null
                (Pay (IdentPay 1) investor issuer (Committed (IdentCC 1)) maturityDate
                    (CommitCash (IdentCC 3) issuer (Value notional) maturityDate (maturityDate + gracePeriod)
                        -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                        (Pay (IdentPay 2) issuer investor (Committed (IdentCC 3))
                            (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                        -- pay from the guarantor otherwise
                        (Pay (IdentPay 3) guarantor investor (Committed (IdentCC 2))
                            (maturityDate + gracePeriod) Null)
                    )
                )
            )
            Null
        )
        Null
```

The client side off-chain test code for the guarantor example, that runs on Mockchain:

```haskell
zeroCouponBondGuaranteedMockchainTest :: Property
zeroCouponBondGuaranteedMockchainTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList    [ (PubKey 1, Ada.adaValueOf 1000000)
                                        , (PubKey 2, Ada.adaValueOf 1000000)
                                        , (PubKey 3, Ada.adaValueOf 1000000) ] }) $ do
    -- Init a contract
    let issuer = Wallet 1
        issuerPk = PubKey 1
        investor = Wallet 2
        investorPk = PubKey 2
        guarantor = Wallet 3
        guarantorPk = PubKey 3
        update = updateAll [issuer, investor, guarantor]
        notional = 1000
        discount = 80
        startDate = 50
        maturityDate = 500
        gracePeriod = 30240 -- about a week, 20sec * 3 * 60 * 24 * 7
    update

    let contract = zeroCouponBondGuaranteed
                        (PubKey 1) (PubKey 2) (PubKey 3) -- parties
                        notional discount -- values
                        startDate maturityDate gracePeriod -- dates

    withContract [issuer, investor, guarantor] contract $ \txOut validator -> do
        -- investor commits money for a bond with discount
        txOut <- investor `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 1) -- commit identifier
            (notional - discount) -- amount of Ada
            emptyState -- initial contract state
            contract   -- initial contract

        update  -- update all participant so they aware about contract being created

        -- guarantor commits a guarantee
        txOut <- guarantor `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 2)
            notional
            -- we expect that previous commit is recorded into Marlowe contract state
            (State [ (IdentCC 1, (PubKey 2, NotRedeemed (notional - discount) maturityDate))] [])
            -- current contract
            (CommitCash (IdentCC 2) guarantorPk (Value notional) startDate (maturityDate + gracePeriod)
                (When FalseObs startDate Null
                    (Pay (IdentPay 1) investorPk issuerPk (Committed (IdentCC 1)) maturityDate
                        (CommitCash (IdentCC 3) issuerPk (Value notional) maturityDate (maturityDate + gracePeriod)
                            -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                            (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 3))
                                (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                            -- pay from the guarantor otherwise
                            (Pay (IdentPay 3) guarantorPk investorPk (Committed (IdentCC 2))
                                (maturityDate + gracePeriod) Null)
                        )
                    )
                )
                Null
            )

        -- move forware in time passing the start date
        addBlocksAndNotify [issuer, investor, guarantor] (startDate + 10)

        -- after startDate the issuer recevies the bond payment
        txOut <- issuer `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 1)
            (notional - discount)
            -- expected state after this state
            (State [(IdentCC 2, (PubKey 3, NotRedeemed notional (maturityDate + gracePeriod)))] [])
            -- expected contract after this step
            (CommitCash (IdentCC 3) issuerPk (Value notional) maturityDate (maturityDate + gracePeriod)
                -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 3))
                    (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                -- pay from the guarantor otherwise
                (Pay (IdentPay 3) guarantorPk investorPk (Committed (IdentCC 2))
                    (maturityDate + gracePeriod) Null)
            )

        -- move forward in time, but before maturity date
        addBlocksAndNotify [issuer, investor, guarantor] 100

        -- before maturityDate the issuer commits the bond value
        txOut <- issuer `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 3)
            notional
            (State [(IdentCC 2, (PubKey 3, NotRedeemed notional (maturityDate + gracePeriod)))] [])
            (CommitCash (IdentCC 3) issuerPk (Value notional) maturityDate (maturityDate + gracePeriod)
                -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 3))
                    (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                -- pay from the guarantor otherwise
                (Pay (IdentPay 3) guarantorPk investorPk (Committed (IdentCC 2))
                    (maturityDate + gracePeriod) Null)
            )

        -- pass the maturity date
        addBlocksAndNotify [issuer, investor, guarantor] maturityDate

        -- after maturity date the investor collects the bond payment
        txOut <- investor `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 2)
            notional
            (State  [ (IdentCC 2, (PubKey 3, NotRedeemed notional (maturityDate + gracePeriod)))] [])
            (RedeemCC (IdentCC 2) Null)

        update

        -- after that guarantor can recall the `guarantee` commit
        txOut <- guarantor `performs` redeem
            txOut
            validator
            [] []
            (IdentCC 2)
            notional
            (State [] [])
            Null

        return (txOut, State [] [])
    return ()
```

### [Prev](./meadow-overview.md) [Up](./Tutorials.md) [Next](./marlowe-plutus.md)
