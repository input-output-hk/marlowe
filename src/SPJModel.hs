module SPJModel where
{-
    Smart Contract model based on "How to write a financial contract" by S.L. Peyton Jones and J-M. Eber
    http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=9DD48728801B6687D982C96FF7406564?doi=10.1.1.14.7885&rep=rep1&type=pdf
-}

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import Control.Monad.State

import qualified Semantics                     as M
import Semantics (Value(..))

data Obs a = Obs a deriving (Eq, Show)

data Currency = GBP | USD | ADA deriving (Eq, Show)

data Contract
    = Zero -- zero is a contract that has no rights and no obligations.
    | One  -- If you acquire (one k) you immediately receive one unit of the currency k .
    | Give Contract -- To acquire (give c) is to acquire all the coounterparty's rights as obligations, and vice versa.
                    -- Note that for a bilateral contract q between parties A and B, A acquiring q
                    -- implies that B acquires (give q).
    | And Contract Contract -- If you acquire (c1 `and ` c2), you immediately acquire both c1 and c2
    | Or  Contract Contract -- If you acquire (c1 `or ` c2) you must immediately acquire your choice of either
                            -- c1 or c2 (but not both).
    | Cond M.Observation Contract Contract -- If you acquire (cond b 1 2), you acquire c1 if the observable b is true at
                                           -- the moment of acquisition, and c2 otherwise.
    | Scale M.Value M.Value Contract   -- If you acquire (scale o c), then you acquire c at the same moment, except
                                       -- that all the payments of c are multiplied by the value of the observable o
                                       -- at the moment of acquisition.
    | When M.Observation Contract  -- If you acquire (when o c), you must acquire c as soon as observable o subsequently
                                   -- becomes True. It is therefore worthless in states where o will never again be True.
    | Anytime M.Observation Contract   -- Once you acquire (anytime o c), you may acquire c at any time the observable
                                       -- o is True. The compound contract is therefore worthless in states
                                       -- where o will never again be True.
    | Until M.Observation Contract -- Once acquired, (until o c) is exactly like c except that it must be abandoned
                                   -- when observable o becomes True. In states in which o is True, the
                                   -- compound contract is therefore worthless, because it must be abandoned immediately.
    deriving (Eq, Show)

maxTimeout :: M.Timeout
maxTimeout = 1234567890 -- FIXME

translateSPJContractToMarlowe :: M.Person -> M.Person -> Contract -> M.Contract
translateSPJContractToMarlowe me counterparty c = case c of
    Zero -> M.Null
    One -> M.Pay (M.IdentPay 1) counterparty me (M.Value 1) maxTimeout M.Null -- TODO should we commit first?
    Give contract -> translateSPJContractToMarlowe counterparty me contract   -- swap me/counterparty
    And c1 c2 -> M.Both (go c1) (go c2)
    Or  c1 c2 -> do
        let choseWhichToAcquire = M.PersonChoseThis (M.IdentChoice 1) me 1
        M.Choice choseWhichToAcquire (go c1) (go c2)
    Cond obs c1 c2 -> M.Choice obs (go c1) (go c2)
    Scale p q contract -> M.Scale p q (go contract)
    When obs contract -> M.When obs maxTimeout (go contract) M.Null
    Anytime obs contract -> do
        let choseToAcquire = M.PersonChoseThis (M.IdentChoice 1) me 1
        M.When (obs `M.AndObs` choseToAcquire) maxTimeout (go contract) M.Null
    Until obs contract -> M.While (M.NotObs obs) maxTimeout (go contract) M.Null
  where
    go = translateSPJContractToMarlowe me counterparty


translateToSPJContract :: M.Person -> M.Person -> M.Contract -> Contract
translateToSPJContract me counterparty m = let
    (letEnv, contract) = translateToSPJContractInner Map.empty me counterparty m
    in contract
  where
    translateToSPJContractInner :: Map M.IdentLet M.Contract -> M.Person -> M.Person -> M.Contract -> (Map M.IdentLet M.Contract, Contract)
    translateToSPJContractInner letEnv me counterparty m = case m of
        M.Null -> (letEnv, Zero)
        M.Pay identPay from to money timeout contract -> do
            let pay = Scale money (Value 1) One
                c   = if from == counterparty then pay else Give pay
            (letEnv, And c (go letEnv contract))
        M.CommitCash ident person money timeout1 timeout2 contract1 contract2 ->
            -- here a user has to decide whether there is enough money to pay, and to consider timeouts
            (letEnv, Or (go letEnv contract1) (go letEnv contract2))
        M.RedeemCC ident contract -> (letEnv, go letEnv contract)
        M.Both c1 c2 -> (letEnv, And (go letEnv c1) (go letEnv c2))
        M.Choice observation c1 c2 -> (letEnv, Cond observation (go letEnv c1) (go letEnv c2))
        M.When observation timeout c1 contract -> (letEnv, When observation (go letEnv c1))
        M.Let ident c1 c2 ->
            let newLetEnv = Map.insert ident c1 letEnv
            in (letEnv, go newLetEnv c2)
        M.Use ident ->
            let c = Maybe.fromMaybe M.Null $ Map.lookup ident letEnv -- TODO Null or error?
            in (letEnv, go letEnv c)

    go letEnv c = snd $ translateToSPJContractInner letEnv me counterparty c

{- model SPJ date observable via block numbers -}

at :: M.BlockNumber -> M.Observation
at block = M.NotObs $ M.BelowTimeout block

-- zero-coupon bond example from SPJ paper
zcb :: M.BlockNumber -> Integer -> Contract
zcb block cash = When (at block) (Scale (Value cash) (Value 1) One)

-- Marlowe implementation of zero-coupon bond example from SPJ paper
zcbMarlowe block cash me person = do
    M.CommitCash (M.IdentCC 1) person (M.Value cash) block maxTimeout -- prepare money for zero-coupon bond, before it could be used
        (M.Pay (M.IdentPay 1) person me (M.Committed (M.IdentCC 1)) maxTimeout M.Null)
        (M.RedeemCC (M.IdentCC 1) M.Null) -- actually, this should not happen.


{- 3.3 Observables and scaling -}
rainInCyprus :: M.Value
rainInCyprus = Value 12

rainInCyprusContract = Cond (M.ValueGE rainInCyprus (Value 10))
    (Scale (Value 10) (Value 1) One)
    (Scale (Value 20) (Value 1) One)

rainInCyprusMarloweContract block me person = do
    let obs = M.ValueGE (M.ValueFromOracle "rainInCyprus" (M.Value 0)) (M.Value 10)
        pay cash = (M.Pay (M.IdentPay 1) person me (M.Value cash) block M.Null)
    M.CommitCash (M.IdentCC 1) person (M.Value 20) block maxTimeout
        (M.When obs maxTimeout (pay 10) (pay 20)) (M.RedeemCC (M.IdentCC 1) M.Null)

{- 3.4 Option contracts -}
between :: Integer -> Integer -> M.Observation
between t1 t2 = M.AndObs (M.NotObs $ M.BelowTimeout t1) (M.BelowTimeout t2)

european :: M.BlockNumber -> Contract -> Contract
european t u = When (at t) (u `Or` Zero)

europeanMarlowe :: M.Timeout -> M.Contract -> M.Contract
europeanMarlowe t c = M.When M.FalseObs t M.Null c

american :: Integer -> Integer -> Contract -> Contract
american t1 t2 u = Anytime (between t1 t2) u


americanMarlowe :: M.Timeout -> M.Timeout -> M.Contract -> M.Contract
americanMarlowe t1 t2 u = M.When M.FalseObs t1 M.Null (M.When M.TrueObs t2 u M.Null)


{- 3.5 Limit contracts -}

interestRate :: Value
interestRate = Value 4

limitContract :: Integer -> Integer -> Contract -> Contract
limitContract t1 t2 c = Until (M.ValueGE interestRate (Value 6)) (american t1 t2 c)

limitContractMarlowe :: M.Timeout -> M.Timeout -> M.Contract -> M.Contract
limitContractMarlowe t1 t2 c = do
    let interestRateObs = M.ValueGE (M.ValueFromOracle "interestRate" (M.Value 0)) (M.Value 6)
        obs = M.NotObs interestRateObs
    M.While obs maxTimeout (americanMarlowe t1 t2 c) M.Null
