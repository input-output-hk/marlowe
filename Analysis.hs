module Analysis where

import Semantics

import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

----------------------
-- Interval algebra --
----------------------

type Interval = (Maybe Int, Maybe Int)
type Domain = [Interval]


-- Comparison of Maybe Ints representing potential infinites
-- a double var in a side means a Nothing on that side
-- represents -inf otherwise it represents +inf

(|<=|) :: Maybe Int -> Maybe Int -> Bool
(|<=|) (Just a) (Just b) = a <= b
(|<=|) Nothing (Just _) = False
(|<=|) _ _ = True

(||<=|) :: Maybe Int -> Maybe Int -> Bool
(||<=|) (Just a) (Just b) = a <= b
(||<=|) _ _ = True

(|<=||) :: Maybe Int -> Maybe Int -> Bool
(|<=||) (Just a) (Just b) = a <= b
(|<=||) _ _ = False

(||<=||) :: Maybe Int -> Maybe Int -> Bool
(||<=||) (Just a) (Just b) = a <= b
(||<=||) Nothing _ = True
(||<=||) _ _ = False

(|>|) :: Maybe Int -> Maybe Int -> Bool
(|>|) a b = not $ (|<=|) a b

(||>|) :: Maybe Int -> Maybe Int -> Bool
(||>|) a b = not $ (||<=|) a b

(|>||) :: Maybe Int -> Maybe Int -> Bool
(|>||) a b = not $ (|<=||) a b

(||>||) :: Maybe Int -> Maybe Int -> Bool
(||>||) a b  = not $ (||<=||) a b

-- Absurd domain detection

possible :: Interval -> Bool
possible (low, high) = low ||<=| high

maybePossible :: Interval -> Maybe Interval
maybePossible i = if (possible i) then Just i else Nothing


-- Example extraction

get_one :: Domain -> Int
get_one [] = error "Empty domain on get_one!"
get_one (h:_) = case h of
                  (Nothing, Nothing) -> 0
                  (Just x, _) -> x
                  (Nothing, Just y) -> y

-- Get first element in Domain


-- Get next element in Domain
next_valid_element :: Int -> Domain -> Maybe Int
next_valid_element _ [] = Nothing
next_valid_element x ((a, b):t)
  | (Just x |>| b) = next_valid_element x t
  | otherwise = case a of
                  Nothing -> Just x
                  Just y -> if (y <= x) then Just x else Just y

-- Element check

is_element :: Int -> Domain -> Bool
is_element _ [] = False
is_element x ((l, h):t)
  | (l ||<=| Just x) && (Just x |<=| h) = True
  | otherwise = is_element x t

-- Generic min and max

mmin_l :: Int -> Maybe Int -> Maybe Int
mmin_l i x = case x of
              Just jx -> Just (min i jx)
              Nothing -> Nothing

mmin_h :: Int -> Maybe Int -> Maybe Int
mmin_h i x = case x of
              Just jx -> Just (min i jx)
              Nothing -> Just (i)

mmax_l :: Int -> Maybe Int -> Maybe Int
mmax_l i x = case x of
              Just jx -> Just (max i jx)
              Nothing -> Just (i)

mmax_h :: Int -> Maybe Int -> Maybe Int
mmax_h i x = case x of
              Just jx -> Just (max i jx)
              Nothing -> Nothing

-- Interval functions
-- ==================

-- Inifite interval
inf_interval :: Interval
inf_interval = (Nothing, Nothing)

-- Inifinite domain
inf_domain :: Domain
inf_domain = [inf_interval]

-- Interval truncating

not_below_int :: Int -> Interval -> Interval
not_below_int i (low, high) = (mmax_l i low, high) 

not_above_int :: Int -> Interval -> Interval
not_above_int i (low, high) = (low, mmin_h i high)

above_int :: Int -> Interval -> Interval
above_int i = not_below_int (i + 1)

below_int :: Int -> Interval -> Interval
below_int i = not_above_int (i - 1)

-- Generic domain wrapper

int_to_domain :: (Int -> Interval -> Interval) -> (Int -> Domain -> Domain)
int_to_domain f i = Maybe.mapMaybe (\d -> maybePossible $ f i d)

-- Does interval include +inf?
unbound_top_int :: Interval -> Bool
unbound_top_int (_, x) = (x == Nothing)

-- Domain truncating

below :: Int -> Domain -> Domain
below = int_to_domain below_int

not_below :: Int -> Domain -> Domain
not_below = int_to_domain not_below_int

above :: Int -> Domain -> Domain
above = int_to_domain above_int

not_above :: Int -> Domain -> Domain
not_above = int_to_domain not_above_int

-- Interval future projection
extend_int :: Interval -> Interval
extend_int (x, _) = (x, Nothing)

-- Domain future projection
extend_dom :: Domain -> Domain
extend_dom (a:_) = [extend_int a]
extend_dom [] = []

-- Make the times in the left domain wait until they reach the right domain
-- assumes the intervals are ordered
wait_interval :: Domain -> Domain -> Domain
wait_interval ((x, y):t) ((x2, y2):t2)
 | (y |<=|| x2) = ((x2, x2):wait_interval t ((x2, y2):t2))
 | (x ||<=|| x2) && (y |<=| y2) = ((x2, y):wait_interval t ((x2, y2):t2))
 | (x ||<=|| x2) && (y |>| y2) = ((x2, y2):wait_interval ((ms y2, y):t) t2)
 | (x ||>|| x2) && (y |<=| y2) = ((x, y):wait_interval t ((x2, y2):t2))
 | (x ||>|| x2) && (x ||<=| y2) && (y |>| y2) = ((x, y2):wait_interval ((y2, y):t) t2)
 | (x ||>| y2) = wait_interval ((x, y):t) t2
 | otherwise = error "Input to wait_interval out of order"
   where ms Nothing = Nothing
         ms (Just n) = Just (n + 1)
wait_interval [] _ = []
wait_interval _ [] = []

-- Does the domain include +inf?
unbound_top :: Domain -> Bool
unbound_top d = any (unbound_top_int) d

intersect_dom :: Domain -> Domain -> Domain
intersect_dom a@((x, y):t) b@((x2, y2):t2)
 | (x2 ||>| y) = intersect_dom t b
 | (x ||<=|| x2) && (y |<=| y2) = ((x2, y):intersect_dom t b)
 | (x ||<=|| x2) && (y |>| y2) = ((x2, y2):intersect_dom a t2)
 | (x ||>|| x2) && (x ||<=| y2) && (y |<=| y2) = ((x, y):intersect_dom t b)
 | (x ||>|| x2) && (x ||<=| y2) && (y |>| y2) = ((x, y2):intersect_dom a t2)
 | (x ||>| y2) = intersect_dom a t2
 | otherwise = error "input to intersect_dom out of order"
intersect_dom [] _ = []
intersect_dom _ [] = []

intersect_dom2 :: [(Domain, Domain)] -> [(Domain, Domain)] -> [(Domain, Domain)]
intersect_dom2 x y = [(intersect_dom a a2, intersect_dom b b2)
                       | (a,b) <- x, (a2, b2) <- y]

-------------------------
-- Analysis data types --
-------------------------

data Event = CashCommit CC
           | CashRedeem RC
           | ValueCommit CV
           | ValueReveal IdentCV Value
           deriving (Eq,Ord,Show,Read)

data EventRecord = PER {
                     block_number :: Domain,
                     etime :: Domain,
                     event :: Event,
                     actions :: [Action]
                     --contract_here :: Contract
                   }
                   deriving (Eq,Ord,Show,Read)

data AnalysisState = AS {
                      curr_event :: Maybe Event,
                      curr_actions :: [Action],
                      possible_block :: Domain,
                      possible_time :: Domain,
                      rem_contract :: Contract,
                      event_record :: [EventRecord],
                      commits :: Commits,
                      state :: State
                    }
                   deriving (Eq,Ord,Show,Read)

------------------------
-- Analysis procedure --
------------------------

has_empty_domain :: AnalysisState -> Bool
has_empty_domain x = (possible_block x == []) || (possible_time x == [])

empty_analysis_state :: Contract -> AnalysisState
empty_analysis_state c = AS {
                          curr_event = Nothing,
                          curr_actions = [],
                          possible_block = inf_domain,
                          possible_time = inf_domain,
                          rem_contract = c,
                          event_record = [],
                          commits = Commits Set.empty Set.empty Map.empty Set.empty,
                          state = (Map.empty, Map.empty)
                         }

add_to_log :: AnalysisState -> AnalysisState
add_to_log (as @ AS {curr_event = Nothing}) = as
add_to_log (as @ AS {curr_event = Just x,
                     curr_actions = cacts,
                     event_record = old_er,
                     possible_time = ptim,
                     possible_block = pblock}) =
    as {event_record = old_er ++ [new_er],
        curr_event = Nothing,
        curr_actions = []}
  where new_er = PER {block_number = pblock,
                      etime = ptim,
                      event = x,
--                      contract_here = rem_contract as,
                      actions = cacts}

analyse_one_step :: AnalysisState -> AnalysisState
analyse_one_step (as@ AS {rem_contract = contr,
                      commits = comm,
                      state = sta,
                      possible_block = blo,
                      possible_time = tim,
                      curr_actions = acts
                     }) =
   add_to_log (as {rem_contract = ncontr,
                   state = nsta,
                   curr_actions = acts ++ nacts})
    where
      (nsta, ncontr, nacts) = full_step comm sta contr (OS {time = get_one tim,
                                                            random = 42, -- ToDo
                                                            blockNumber = get_one blo})

-- Analyses possible combinations of observables

-- Remove top actions from contract (including those in Both trees)
remove_actions :: Contract -> Contract
remove_actions (Both contr1 contr2) = (Both (remove_actions contr1) (remove_actions contr2))
remove_actions (CommitValue _ _ _ contr) = contr
remove_actions (CommitCash _ _ _ _ contr) = contr
remove_actions (RevealCV _ contr) = contr
remove_actions (RedeemCC _ contr) = contr
remove_actions contr = contr

interval_from_obs :: Map.Map IdentCV Value -> Observation -> [(Domain, Domain)]
interval_from_obs _ (TimeAbove n) = [(inf_domain, above n inf_domain)]
interval_from_obs _ (BelowTimeout n) = [(below n inf_domain, inf_domain)]
interval_from_obs m (AndObs obs1 obs2) = intersect_dom2 (interval_from_obs m obs1)
                                                        (interval_from_obs m obs2)
interval_from_obs m (OrObs obs1 obs2) = (interval_from_obs m obs1) ++
                                        (interval_from_obs m obs2)
interval_from_obs m (CVRevealedAs ident v) =
   if x == Just v then interval_from_obs m TrueObs else interval_from_obs m FalseObs
  where x = Map.lookup ident m
interval_from_obs _ (TrueObs) = [(inf_domain, inf_domain)]
interval_from_obs _ (FalseObs) = []
interval_from_obs m (NotObs o) = interval_from_obs_inv m o

interval_from_obs_inv :: Map.Map IdentCV Value -> Observation -> [(Domain, Domain)]
interval_from_obs_inv _ (TimeAbove n) = [(inf_domain, not_above n inf_domain)]
interval_from_obs_inv _ (BelowTimeout n) = [(not_below n inf_domain, inf_domain)]
interval_from_obs_inv m (AndObs obs1 obs2) = (interval_from_obs m obs1) ++
                                             (interval_from_obs m obs2)
interval_from_obs_inv m (OrObs obs1 obs2) = intersect_dom2 (interval_from_obs m obs1)
                                                           (interval_from_obs m obs2)
interval_from_obs_inv m (CVRevealedAs ident v) =
   if x == Just v then interval_from_obs_inv m TrueObs else interval_from_obs_inv m FalseObs
  where x = Map.lookup ident m
interval_from_obs_inv _ (FalseObs) = [(inf_domain, inf_domain)]
interval_from_obs_inv _ (TrueObs) = []
interval_from_obs_inv m (NotObs o) = interval_from_obs m o


analyse_one_step_observables_aux :: Contract -> AnalysisState -> [AnalysisState]
analyse_one_step_observables_aux (Choice (TimeAbove tim) _ _)    -- TimeAbove
                                 (as@ AS {possible_time = ptime}) =
   [as {possible_time = above tim ptime},
    as {possible_time = not_above tim ptime}]
analyse_one_step_observables_aux (Choice (BelowTimeout tim) _ _) -- BelowTimeout
                                 (as@ AS {possible_block = pblo}) =
   [as {possible_block = below tim pblo},
    as {possible_block = not_below tim pblo}]
analyse_one_step_observables_aux (Choice (AndObs obs1 obs2) c1 c2) as = -- AndObx
   List.concatMap (analyse_one_step_observables_aux (Choice obs2 c1 c2)) $
        analyse_one_step_observables_aux (Choice obs1 c1 c2) as
analyse_one_step_observables_aux (Choice (OrObs obs1 obs2) c1 c2) as = -- OrObs
   List.concatMap ((flip analyse_one_step_observables_aux) as)
                  [Choice obs1 c1 c2, Choice obs2 c1 c2]
analyse_one_step_observables_aux (When obs tim _ _) -- When 
                                 as@ AS {possible_time = ptime,
                                         possible_block = pblock,
                                         commits = Commits {rv = rv_old}} =
    [as {possible_time = wait_interval ptime pt,
         possible_block = below tim (wait_interval (below tim pblock) pb)}
      | (pt, pb) <- interval_from_obs rv_old obs] ++ [aft]
   where aft = as {possible_block = not_below tim pblock}
analyse_one_step_observables_aux _ as = [as]

analyse_one_step_observables :: AnalysisState -> [AnalysisState]
analyse_one_step_observables as =
  analyse_one_step_observables_aux (remove_actions (rem_contract as)) as

-- Analyses possible combinations of actions regarding the root node
analyse_one_step_action_aux :: AnalysisState -> [AnalysisState]
analyse_one_step_action_aux (as@ AS {rem_contract = (CommitCash ident per cash tout _),
                                     commits = comm@Commits {cc = cc_old}, -- CommitCash
                                     possible_block = blo
                                    }) =
       [ -- the commit is done on time
        as {possible_block = below tout blo,
            commits = comm {cc = Set.insert cc_new cc_old},
            curr_event = Just $ CashCommit cc_new},
         -- the commit is not done on time
        as {possible_block = not_below tout blo,
            commits = comm }
       ]
    where cc_new = (CC ident per cash tout)
analyse_one_step_action_aux (as@ AS {rem_contract = (CommitValue ident per _ _),
                                     commits = comm@Commits {cv = cv_old}, -- CommitValue
                                     possible_block = blo,
                                     possible_time = tim
                                   }) =
       [ -- the commit is done on time
        as { -- no timeout
            commits = comm {cv = Set.insert cv_new cv_old},
            curr_event = Just $ ValueCommit cv_new,
            possible_block = extend_dom blo,
            possible_time = extend_dom tim},
        as
         -- the commit is not done on time (not possible yet)
       ]
    where cv_new = (CV ident per)
analyse_one_step_action_aux (as@ AS {rem_contract = (RevealCV ident _),
                                     commits = comm@Commits {rv = rv_old}, -- RevealCV
                                     possible_block = blo,
                                     possible_time = tim,
                                     state = sta
                                    }) =
       [let rv_new = Map.insert ident val rv_old in -- if not is_reveal this does nothing
        as {commits = comm {rv = rv_new},
            possible_block = extend_dom blo,
            possible_time = extend_dom tim,
            curr_event = if is_new_reveal
                         then Just $ ValueReveal ident val
                         else Nothing}
        | val <- values] ++ [as]
    where (is_new_reveal, ev) = case Map.lookup ident rv_old of
                                  Nothing -> (True, error "It is new RevealCV in analysis!")
                                  Just x -> (False, x)
          values = case Map.lookup ident cvs of
                     Just (Unrevealed vals) -> if is_new_reveal
                                               then vals
                                               else [ev]
                     _ -> []
          (cvs,_) = sta
analyse_one_step_action_aux (as@ AS {rem_contract = (RedeemCC ident _),
                                     commits = comm@Commits {rc = rc_old}, -- RedeemCC
                                     state = sta
                                    }) =
    case Map.lookup ident ccs of
      Just (_, NotRedeemed val _) ->
                 let rc_new  = (RC ident val) in 
                   [as { commits = comm {rc = Set.insert rc_new rc_old },
                         curr_event = Just $ CashRedeem rc_new}, as]
      _ -> [as]
    where (_,ccs) = sta
analyse_one_step_action_aux (as@ AS {rem_contract = contr@(Both con1 con2)}) = -- Both
    map (\x -> x {rem_contract = contr}) $
    List.concatMap (analyse_one_step_action_aux . (\x -> x {rem_contract = con2}))
                   (analyse_one_step_action_aux (as {rem_contract = con1}))
analyse_one_step_action_aux as = [as]
        
analyse_one_step_action :: AnalysisState -> [AnalysisState]
analyse_one_step_action as = List.concatMap (analyse_one_step_observables)
                               (analyse_one_step_action_aux as)

-- Analyses possible combinations of timeouts in commits 
analyse_one_step_commits_aux :: AnalysisState -> [AnalysisState]
analyse_one_step_commits_aux (as @ AS {state = (_, ccst)}) =
  split_by_block_list as $ List.sort $ List.nub $
    Maybe.mapMaybe extract_expdate $ Map.elems ccst

split_by_block_list :: AnalysisState -> [Int] -> [AnalysisState]
split_by_block_list as [] = [as]
split_by_block_list as (h:t) = (this:split_by_block_list rest t)
  where rest = apply_to_as (not_below h)
        this = apply_to_as (below h)
        apply_to_as f = (as {possible_block = f (possible_block as)})

extract_expdate :: CCstatus -> Maybe ExpiryTime
extract_expdate (_, NotRedeemed _ ee) = Just ee
extract_expdate _ = Nothing

analyse_one_step_commits :: AnalysisState -> [AnalysisState]
analyse_one_step_commits as = List.concatMap (analyse_one_step_action)
                                (analyse_one_step_commits_aux as)

analyse_one_step_split :: AnalysisState -> [AnalysisState]
analyse_one_step_split as = map analyse_one_step $
                                   List.concatMap (analyse_one_step_commits) [as]

expand_if_null :: AnalysisState -> AnalysisState
expand_if_null (as @ AS {rem_contract = Null,
                         possible_block = blo,
                         possible_time = tim}) =
            as {possible_block = extend_dom blo,
                possible_time = extend_dom tim}
expand_if_null as = as

analysis_step :: [AnalysisState] -> [AnalysisState]
analysis_step as = filter (not . has_empty_domain) $
                       List.concatMap (analyse_one_step_split . expand_if_null) as

-- Harness: Calls analysis function until nothing happens
analysis_full :: [AnalysisState] -> [AnalysisState]
analysis_full as
  | as == nas = as
  | otherwise = analysis_full nas
  where nas = List.nub (analysis_step as)

analysis :: Contract -> [AnalysisState]
analysis c = analysis_full [empty_analysis_state c]

get_unique_action_seqs :: [AnalysisState] -> [[Action]]
get_unique_action_seqs x = List.nub $
                            map (get_actions) x

get_actions :: AnalysisState -> [Action]
get_actions y = concat $ concat [map actions (event_record y), [curr_actions y]]

filter_by_action_seq :: [Action] -> [AnalysisState] -> [AnalysisState]
filter_by_action_seq x = filter (\y -> get_actions y == x)

-- Removes states with contracts that did not reduce to null
only_null :: [AnalysisState] -> [AnalysisState]
only_null x = filter (\y -> rem_contract y == Null) x

-- Finds states where there is unexecuted contract
only_not_null :: [AnalysisState] -> [AnalysisState]
only_not_null x = filter (\y -> rem_contract y /= Null) x

-- Finds states that will not be changed by the action of time
only_stable :: [AnalysisState] -> [AnalysisState]
only_stable = filter fil
     where fil y = (unbound_top (possible_block y)) && (unbound_top (possible_time y))



