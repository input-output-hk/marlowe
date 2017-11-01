module Semantics6 where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List


 -------------------------------------------------------------------------------------------------
 --                                                                                             --
 -- Prototype implementation of a small DSL for commit/redeem based contracts on blockchain     --
 --                                                                                             --
 -- Structured thus:                                                                            --
 --     - basic data types                                                                      --
 --     - type of Actions (to be performed on the blockchain as a result of contract evaluation --
 --     - type of Observables (quantities which can be observed and recorded on blockchain)     --
 --     - types of Commitments (of values and of cash)                                          --
 --     - type of State (of the internal state of a DSL contract evaluation)                    --
 --     - type of Observations (of values of Observables)                                       --
 --     - type of Contracts                                                                     --
 --     - single step evaluation (the step function) which is wrapped by full_step …            --
 --     - … which expires and refunds cash commitments                                          --
 --                                                                                             --
 -- Further discussion in accompanying document.                                                --
 -------------------------------------------------------------------------------------------------

{----------------------
 -- Basic data types --
 ----------------------} 

type Key = Int -- Public key

type Person      = Key
type Time        = Int -- computation steps
type Random      = Int
type BlockNumber = Int

-- Actions are things that have an effect on the blockchain.
-- The current implementation doesn't properly reflect this.
-- TO BE DONE

data Action =   SuccessfulPay Person Person Cash |
                FailedPay Person Person Cash |
                SuccessfulCommit Person Cash |
                ExpiredRedeem Person |
                DuplicateRedeem Person |
                DuplicateReveal IdentCV 
                    deriving (Eq,Ord,Show,Read)

type AS = [Action]

-- Observables are things which are recorded on the blockchain.
--  e.g. "a random choice", the value of GBP/BTC exchange rate, …

-- Question: how do we implement these things?
--  - We assume that some mechanism exists which will ensure that the value is looked up and recorded, or …
--  - … we actually provide that mechanism explicitly, e.g. with inter-contract comms or transaction generation or something.

data Observable = Time | Random | BlockNumber
                    deriving (Eq,Ord,Show,Read)

data OS =  OS { time         :: Time,
                random       :: Random,
                blockNumber  :: BlockNumber}
                    deriving (Eq,Ord,Show,Read)

-- Commitments
--  Types for cash and value commits and reveals.
--  The type CR collects the sets of commits/reveals at a given point
--  during execution.

type Value    = Int
 
type Cash     = Int

type ExpiryTime = BlockNumber

data IdentCV = IdentCV Int
               deriving (Eq,Ord,Show,Read)
data IdentCC = IdentCC Int
               deriving (Eq,Ord,Show,Read)

data CV = CV IdentCV Person
               deriving (Eq,Ord,Show,Read)
data CC = CC IdentCC Person Cash ExpiryTime
               deriving (Eq,Ord,Show,Read)
data RC = RC IdentCC Cash
               deriving (Eq,Ord,Show,Read)

data Commits = Commits {
                cv  :: Set.Set CV,
                cc  :: Set.Set CC,
                rv  :: Map.Map IdentCV Value,
                rc  :: Set.Set RC
              }
               deriving (Eq,Ord,Show,Read)

-- A type of states; this represents part of the state that needs to be
-- stored on the blockchain.
--
-- Observations of observables also need to be stored on the blockchain,
-- so that computations can be re-run. Recording these should be seen as
-- a side-effect of their evaluation.

type State = (Map.Map IdentCV CVstatus, Map.Map IdentCC CCstatus)

data CVstatus = Unrevealed [Value] | Revealed Value
               deriving (Eq,Ord,Show,Read)

type CCstatus = (Person,CCredeemStatus)
data CCredeemStatus = NotRedeemed Cash ExpiryTime | TimedOut | ManuallyRedeemed
               deriving (Eq,Ord,Show,Read)


-- Representation of observations over observables and the state.
-- Rendered into predicates by interpretObs.

-- TO DO: add enough operations to make complete for arithmetic etc.
-- as well as enough primitive observations over the primitive values.


data Observation =  TimeAbove Int |
                    BelowTimeout BlockNumber | -- is this number below the actual block number?
                    AndObs Observation Observation |
                    OrObs Observation Observation |
                    NotObs Observation |
                    CVRevealedAs IdentCV Value |
                    TrueObs | FalseObs
                    deriving (Eq,Ord,Show,Read)

-- Semantics of observations
                    
interpretObs :: State -> Observation -> OS -> Bool

interpretObs _ (TimeAbove n) os
    = time os > n
interpretObs _ (BelowTimeout n) os
    = not $ expired (blockNumber os) n
interpretObs st (AndObs obs1 obs2) os
    = interpretObs st obs1 os && interpretObs st obs2 os
interpretObs st (OrObs obs1 obs2) os
    = interpretObs st obs1 os || interpretObs st obs2 os
interpretObs st (NotObs obs) os
    = not (interpretObs st obs os)
interpretObs st (CVRevealedAs ident m) _
    = case Map.lookup ident (fst st) of
        Nothing -> False
        Just (Unrevealed _) -> False
        Just (Revealed n)   -> n==m
interpretObs _ (TrueObs) _
    = True
interpretObs _ (FalseObs) _
    = False

-- The type of contracts

data Contract =
    Null |
    RedeemCC IdentCC Contract |
    RevealCV IdentCV Contract |
    Pay Person Person Int Contract |
    Both Contract Contract |
    Choice Observation Contract Contract |
    CommitValue IdentCV Person [Value] Contract |
    CommitCash IdentCC Person Cash Time Contract |
    When Observation Time Contract Contract
               deriving (Eq,Ord,Show,Read)


{-------------
 - Semantics -
 -------------}

-- A single computation step in evaluating a contract.

step :: Commits -> State -> Contract -> OS -> (State,Contract,AS)

step _ st Null _ = (st, Null, [])

step _ st (Pay from to val con) os =
    if
        committed st from bn >= val
    then
        (newstate,con,[SuccessfulPay from to val])
    else
        (st,con,[FailedPay from to val])
    where
        newstate = stateUpdate st from to bn val
        bn = blockNumber os


-- CHECK: the clause for Both could use a commitment twice,
-- but only if the identity is duplicated, and should not be possible.

step comms st (Both con1 con2) os =
    (st2, result, ac1 ++ ac2)
    where
        result = if res1==Null
                    then res2
                    else if res2==Null
                        then res1
                        else Both res1 res2
        (st1,res1,ac1) = step comms st con1 os
        (st2,res2,ac2) = step comms st1 con2 os

step _ st (Choice obs conT conF) os =
    if interpretObs st obs os
        then (st,conT,[])
        else (st,conF,[])

step _ st (When obs expi con con2) os =
    if (expired (blockNumber os) expi)
    then (st,con2,[])
    else (if interpretObs st obs os
          then (st,con,[])
          else (st,(When obs expi con con2),[]))

step commits st c@(CommitValue ident person values con) _ =
    if
        Set.member (CV ident person) (cv commits)
    then
        (newstate,con,[])
    else
        (st,c,[])
    where
        (cvs,ccs) = st
        newstate  = (Map.insert ident (Unrevealed values) cvs, ccs)

-- Note that conformance of the commitment here is exact
-- May want to relax this

step commits st c@(CommitCash ident person val timeout con) os =
    if (cex)
    then (ust, con, [SuccessfulCommit person val,
                     SuccessfulPay person person val])
    else if Set.member (CC ident person val timeout) (cc commits)
         then (ust, con, [SuccessfulCommit person val])
         else (st, c, [])
    where
         (cvs, ccs) = st
         cex = (expired (blockNumber os) (timeout))
         cns = (person, (if cex
                         then TimedOut
                         else (NotRedeemed val timeout)))
         ust = (cvs, Map.insert ident cns ccs)

-- Note: there is no possibility of payment failure here: is that correct?
-- Also: look at partial redemption: currently it is all or nothing.

step commits st c@(RedeemCC ident con) _ =
    case Map.lookup ident ccs of
      Just (person, NotRedeemed val _) ->
        let newstate = (cvs, Map.insert ident (person, ManuallyRedeemed) ccs) in
        if (Set.member (RC ident val) (rc commits))
        then (newstate, con, [SuccessfulPay person person val])
        else (st, c, [])
      Just (person, ManuallyRedeemed) ->
        (st, con, [DuplicateRedeem person])
      Just (person, TimedOut) ->
        let newstate = (cvs, Map.insert ident (person, ManuallyRedeemed) ccs) in
        (newstate, con, [ExpiredRedeem person])
      Nothing -> (st,c,[])
    where
        (cvs,ccs) = st

step commits st c@(RevealCV ident con) _ =
    case
        Map.lookup ident (rv commits)
    of
        Just val -> case
                      Map.lookup ident cvs
                    of
                      Just (Unrevealed vals) ->
                          let newstate = (Map.insert ident (Revealed val) cvs, ccs) in
                               if (elem val vals)
                               then (newstate, con, [])
                               else (st,c,[])
                      Just (Revealed _) ->
                                 (st,con,[DuplicateReveal ident])         
                      Nothing -> (st,c,[])
        Nothing  -> (st,c,[])
      where
        (cvs,ccs) = st

-- Wraps step function to refund expired cash commitments

full_step :: Commits -> State -> Contract -> OS -> (State,Contract,AS)

full_step com (cvst, ccst) con os = (rs, rcon, pas ++ ras)
  where (expi, nccst) = Map.partition (isExpiredNotRedeemed et) ccst 
        pas = [SuccessfulPay p p val | (_, (p, NotRedeemed val _)) <- Map.toList expi]
        et = blockNumber os
        uexp = Map.map (auto_expire) expi
        (rs, rcon, ras) = step com (cvst, Map.union (uexp) (nccst)) con os

auto_expire :: CCstatus -> CCstatus

auto_expire (p, NotRedeemed _ _) = (p, TimedOut)
auto_expire (p, x) = (p, x)


-- Auxiliary functions on the state

-- How much money is committed by a person, and is still unexpired?

committed :: State -> Person -> BlockNumber -> Cash

committed (_,ccl) per current_block = sum [ v | c@(_, NotRedeemed v _) <- Map.elems ccl, isRedeemable per current_block c ]

-- Assume this is only called when there is enough cash available.

stateUpdate :: State -> Person -> Person -> ExpiryTime -> Cash -> State

stateUpdate st from _ bn val =
    (cvs,newccs)
    where
        (cvs,ccs) = st
        newccs = updateMap ccs from bn val

-- Take Cash amount from Person commitments unexpired at time ExpiryTime, giving
-- priority to those that expire earliest.

updateMap :: Map.Map IdentCC CCstatus -> Person -> ExpiryTime -> Cash -> Map.Map IdentCC CCstatus
updateMap mx p e v = discountFromValid (isRedeemable p e) v (mx)

-- Does this particular map-record for a commitment belong to the person,
-- and is it unexpired?

isRedeemable :: Person -> ExpiryTime -> CCstatus -> Bool
isRedeemable p e (ep, NotRedeemed _ ee) = (ep == p) && (not (expired e ee))
isRedeemable _ _ _  = False 

-- Is this particular map-record for a commitment not-redeemed but expired?
isExpiredNotRedeemed :: ExpiryTime -> CCstatus -> Bool
isExpiredNotRedeemed e (_, NotRedeemed _ ee) = (expired e ee)
isExpiredNotRedeemed _ (_, _) = False 

-- Defines if expiry time ee has come if current time is e
expired :: ExpiryTime -> ExpiryTime -> Bool
expired e ee = (ee <= e)

-- Removes the total Cash from those entries in the map that
-- meet the filter function, passed as first argument.

discountFromValid :: (CCstatus -> Bool) -> Cash -> Map.Map IdentCC CCstatus -> Map.Map IdentCC CCstatus
discountFromValid f v m = updated_map
  where redeemable_submap = Map.filter f m
        ordered_redeemable_list = sortByExpirationDate (Map.toList redeemable_submap)
        changes_to_map = discountFromPairList v ordered_redeemable_list
        updated_map = Map.union (Map.fromList changes_to_map) m

-- Discounts the Cash from an initial segment of the list of pairs.

discountFromPairList :: Cash -> [(IdentCC, CCstatus)] -> [(IdentCC, CCstatus)]
discountFromPairList v ((ident, (p, NotRedeemed ve e)):t)
  | v <= ve = [(ident, (p, NotRedeemed (ve - v) e))]
  | ve < v = (ident, (p, NotRedeemed 0 e)):(discountFromPairList (v - ve) t)
discountFromPairList _ (_:t) = t 
discountFromPairList _ _ = error "attempt to discount when insufficient cash available"

-- Sorts a list of pairs by expiration date.

sortByExpirationDate :: [(IdentCC, CCstatus)] -> [(IdentCC, CCstatus)]
sortByExpirationDate l = List.sortBy (lower_expiration_date_but_not_expired) l

lower_expiration_date_but_not_expired :: (IdentCC, CCstatus) -> (IdentCC, CCstatus) -> Ordering

lower_expiration_date_but_not_expired (_, (_, NotRedeemed _ e)) (_, (_, NotRedeemed _ e2)) = compare e e2
lower_expiration_date_but_not_expired (_, (_, NotRedeemed _ _)) _ = LT 
lower_expiration_date_but_not_expired _ (_, (_, NotRedeemed _ _)) = GT
lower_expiration_date_but_not_expired _ _ = EQ 

{----------
 - Driver -
 ----------}

-- Driver for a single step of execution, using the full_step function
-- This first performs any repayments due because of an expired commit,
-- then calls the step function.

-- Given a start state, a contract and a stream of commits and observables,
-- produces a list of actions to perform at each step.

driver :: State -> Contract -> [(Commits,OS)] -> [AS]

driver start_state contract input =
    aset:rest
    where
        (com1,os1):rest_input   = input
        (next_st,next_con,aset) = full_step com1 start_state contract os1
        rest                    = driver next_st next_con rest_input

--

input_stream :: Commits -> [(Commits,OS)]

input_stream commits =
    result
    where
        result         = zip commits_stream os_stream
        commits_stream = repeat commits
        os_stream      = zipWith3 OS [1..] (repeat 42) (concat (map (replicate 100) [1..]))

