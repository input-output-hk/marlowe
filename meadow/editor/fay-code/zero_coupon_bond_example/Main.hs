module Main where

import Marlowe
import Fay.FFI (ffi)

setCode :: String -> Fay ()
setCode = ffi "textarea.setValue(%1)"

main :: Fay ()
main = setCode (prettyPrintContract contract)

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Zero Coupon Bond example using embedding

contract :: Contract
contract = zeroCouponBond 1 2 1000 200 10 20 30

zeroCouponBond :: Person -> Person -> Money -> Money -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBond issuer investor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    CommitCash (IdentCC 1) investor (ConstMoney (notional - discount)) startDate maturityDate
        -- issuer must commit a full notional value of a bond
        (CommitCash (IdentCC 2) issuer (ConstMoney notional) startDate (maturityDate + gracePeriod)
            (When FalseObs startDate Null
                -- after start date but before maturity date the issuer can receive the bond payment
                (Pay (IdentPay 1) investor issuer (AvailableMoney (IdentCC 1)) maturityDate
                    (When FalseObs maturityDate Null
                        -- after maturity date the investor can claim bond's full value
                        (Pay (IdentPay 2) issuer investor (AvailableMoney (IdentCC 2))
                            (maturityDate + gracePeriod) Null)
                    )
                )
            )
            Null
        )
        Null

