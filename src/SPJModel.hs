{-
    Smart Contract model based on "How to write a financial contract" by S.L. Peyton Jones and J-M. Eber
    http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=9DD48728801B6687D982C96FF7406564?doi=10.1.1.14.7885&rep=rep1&type=pdf
-}

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.State

import qualified Semantics                     as M

data Obs a = Obs a deriving (Eq, Show)

data Currency = GBP | USD | ADA deriving (Eq, Show)

data Contract
    = Zero
    | One Currency
    | Give Contract
    | And Contract Contract
    | Or  Contract Contract
    | Cond (Obs Bool) Contract Contract
    | Scale (Obs Double) Contract
    | When (Obs Bool) Contract
    | Anytime (Obs Bool) Contract
    | Until (Obs Bool) Contract
    deriving (Eq, Show)

constObs :: a -> Obs a
constObs a = Obs a

lift2 f (Obs a) (Obs b) = Obs (f a b)

instance Num a => Num (Obs a) where
    fromInteger i = constObs (fromInteger i )
    (+) = lift2 (+)
    (-) = lift2 (-)
    (*) = lift2 (*)

maxTimeout :: M.Timeout
maxTimeout = 1234567890 -- FIXME

translateSPJContractToMarlowe :: M.Person -> M.Person -> Contract -> M.Contract
translateSPJContractToMarlowe me counterparty c = case c of
    Zero -> M.Null
    One ADA  -> M.Pay (M.IdentPay 1) counterparty me (M.ConstMoney 1) maxTimeout M.Null -- TODO should we commit first?
    One curr  -> undefined -- TODO only ADA for now
    Give contract -> translateSPJContractToMarlowe counterparty me contract -- swap me/counterparty
    And c1 c2 -> M.Both (go c1) (go c2)
    Or  c1 c2 -> do
        -- not sure, M.Choice should be here, but I didn't understand how it's supposed to be choosen in SPJ paper.
        -- looks like it should be an input of some kind
        let obs = M.TrueObs -- TODO mock
        M.Choice obs (go c1) (go c2)
    Cond obs c1 c2 -> M.When (translateObsToMarlowe obs) maxTimeout (go c1) (go c2)
    Scale obs contract -> undefined -- TODO scaleContract obs contract. Introduce into Marlowe?
    When obs contract -> M.When (translateObsToMarlowe obs) maxTimeout (go contract) M.Null
    Anytime obs contract -> M.When (translateObsToMarlowe obs) maxTimeout (go contract) M.Null
    Until obs contract -> M.When (M.NotObs $ translateObsToMarlowe obs) maxTimeout (go contract) M.Null
  where
    go = translateSPJContractToMarlowe me counterparty


translateObsToMarlowe o = undefined

{-
    Not that straightforward... We need State and Input here.
    Basically we need this to me inside M.step function.
    Just a template for now
-}
translateToSPJContract :: M.Contract -> Contract
translateToSPJContract m = case m of
    M.Null -> Zero
    M.Pay ident from to (M.ConstMoney cash) timeout cont -> Scale (constObs (fromInteger cash)) (One ADA)
    M.Pay identPay from to money timeout contract -> do
        let cash = M.evalMoney (M.emptyState) M.emptyOS money
        Scale (constObs (fromInteger cash)) (One ADA)
        -- 
    M.CommitCash ident person money timeout1 timeout2 contract1 contract2 -> Zero
    M.RedeemCC ident contract -> Zero
    M.Both c1 c2 -> And (translateToSPJContract c1) (translateToSPJContract c2)
    M.Choice observation c1 c2 -> Cond (translateObsToSPJ observation) (translateToSPJContract c1) (translateToSPJContract c2)
    M.When observation timeout c1 contract -> Zero

translateObsToSPJ obs = constObs $ M.interpretObs (M.emptyState) obs (M.emptyOS) -- TODO full implementation, needs State

{- model SPJ date observable via block numbers -}

currentBlock :: Obs Integer
currentBlock = undefined

at :: M.BlockNumber -> Obs Bool
at block = let Obs cb = currentBlock in Obs (cb >= block)

-- zero-coupon bond example from SPJ paper
zcb :: M.BlockNumber -> Double -> Contract
zcb block cash = When (at block) (Scale (constObs cash) (One USD))

-- Marlowe implementation of zero-coupon bond example from SPJ paper
zcbMarlowe block cash me person = do
    M.CommitCash (M.IdentCC 1) person (M.ConstMoney cash) block maxTimeout -- prepare money for zero-coupon bond, before it could be used
        (M.Pay (M.IdentPay 1) person me (M.AvailableMoney (M.IdentCC 1)) maxTimeout M.Null) 
        (M.RedeemCC (M.IdentCC 1) M.Null) -- actually, this should not happen.

        
{- 3.3 Observables and scaling -}
rainInCyprus :: Obs Double
rainInCyprus = Obs 12.5

rainInCyprusContract = Cond (lift2 (>) rainInCyprus (constObs 10.0)) (One GBP) (One USD)

rainInCyprusMarloweContract block me person = do
    let obs = M.ValueGE (M.MoneyFromOracle "rainInCyprus" (M.ConstMoney 0)) (M.ConstMoney 10)
        pay cash = (M.Pay (M.IdentPay 1) person me (M.ConstMoney cash) block M.Null)
    M.CommitCash (M.IdentCC 1) person (M.ConstMoney 20) block maxTimeout 
        (M.When obs maxTimeout (pay 10) (pay 20)) (M.RedeemCC (M.IdentCC 1) M.Null)

{- 3.4 Option contracts -}
between :: Integer -> Integer -> Obs Bool
between t1 t2 = lift2 (&&) (lift2 (>=) currentBlock (constObs t1)) (lift2 (<=) currentBlock (constObs t2))

european :: M.BlockNumber -> Contract -> Contract
european t u = When (at t) (u `Or` Zero)

europeanMarlowe :: M.Timeout -> M.Contract -> M.Contract
europeanMarlowe t c = M.When M.FalseObs t M.Null c

american :: Integer -> Integer -> Contract -> Contract
american t1 t2 u = Anytime (between t1 t2) u


americanMarlowe :: M.Timeout -> M.Timeout -> M.Contract -> M.Contract
americanMarlowe t1 t2 u = M.When M.FalseObs t1 M.Null (M.When M.TrueObs t2 u M.Null)


{- 3.5 Limit ontrats -}

interestRate :: Obs Integer
interestRate = Obs 4

limitContract :: Integer -> Integer -> Contract -> Contract
limitContract t1 t2 c = Until (lift2 (>) interestRate (constObs 6)) (american t1 t2 c)

limitContractMarlowe :: M.Timeout -> M.Timeout -> M.Contract -> M.Contract
limitContractMarlowe t1 t2 c = do
    let interestRateObs = M.ValueGE (M.MoneyFromOracle "interestRate" (M.ConstMoney 0)) (M.ConstMoney 6) 
        obs = M.NotObs interestRateObs
    M.When obs maxTimeout (americanMarlowe t1 t2 c) M.Null

{-
    Questions:
    1. CommitCash/RedeemCC before SPJ Contract based on max evaluation?
    2. Builder API for IdentCC etc
    3. Extend Observation with math, API for extenal values
    4. How to encode SPJ 'or' (choosing which contract to continue)?
    5. Translate SPJ observables into timeouts.
-}

main :: IO ()
main = do
    print $ zcbMarlowe 100 12345 1 2
    -- putStrLn (show (translateToSPJContract M.Null))
    let c = One
    print $ translateSPJContractToMarlowe 1 8 (One ADA)
    print $ translateSPJContractToMarlowe 1 8 (Give $ One ADA)
