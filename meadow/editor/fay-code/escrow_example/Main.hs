module Main where

import Marlowe
import Fay.FFI (ffi)

setCode :: String -> Fay ()
setCode = ffi "document.getElementById('textarea').value = %1"

main :: Fay ()
main = setCode (prettyPrintContract contract)

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Escrow example using embedding

contract :: Contract
contract = CommitCash iCC1 1
                      (ConstMoney 450)
                      10 100
                      (When (OrObs (two_chose 1 2 3 0)
                                   (two_chose 1 2 3 1))
                            90
                            (Choice (two_chose 1 2 3 1)
                                    (Pay iP1 1 2
                                         (AvailableMoney iCC1)
                                         100
                                         redeem_original)
                                    redeem_original)
                            redeem_original)
                      Null

chose :: Int -> ConcreteChoice -> Observation
chose per c =  PersonChoseThis (IdentChoice per) per c

one_chose :: Person -> Person -> ConcreteChoice -> Observation
one_chose per per' val = (OrObs (chose per val) (chose per' val)) 
                                  
two_chose :: Person -> Person -> Person -> ConcreteChoice -> Observation
two_chose p1 p2 p3 c = OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))
                             (AndObs (chose p2 c) (chose p3 c))

redeem_original :: Contract
redeem_original = RedeemCC iCC1 Null

iCC1 :: IdentCC
iCC1 = IdentCC 1

iP1 :: IdentPay
iP1 = IdentPay 1


