module Futures where

import Minimal

alicePk = 1
bobPk = 2

contract :: Contract
contract = do
    let penalty = 1000
    let forwardPrice = 1123
    let units = 187
    let deliveryDate = 100
    let endTimeout = deliveryDate + 50
    let startTimeout = 10
    let oraclePk = 3 :: Integer
    let initialMargin = penalty + (units * forwardPrice `div` 20) -- 5%, 11500
    let forwardPriceV = Constant forwardPrice
    let spotPrice = 1124
    let spotPriceV = OracleValue (OracleId oraclePk) (Constant forwardPrice)
    let diff = Constant initialMargin `SubValue`
                    MulValue (Constant units) (SubValue forwardPriceV spotPriceV)
    let contract = When [
            Case (AndObs (ValueEQ (CommittedBy alicePk) (Constant initialMargin))
                         (ValueEQ (CommittedBy bobPk) (Constant initialMargin)))
                    (When [] deliveryDate (Pay [(diff, alicePk)] (Left bobPk)))
            ] startTimeout
            (Pay [(CommittedBy alicePk, alicePk)] (Left bobPk))
    contract