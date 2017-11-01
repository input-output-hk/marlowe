module RPS where

import qualified Data.Set as Set
import qualified Data.Map as Map

import Semantics6    

-------------------------------------------------------------
-- Implementation of a single round of rock-paper-scissors --
-------------------------------------------------------------

timeout :: Time

timeout = 42  

-- generic functions --

or_compose :: [Observation] -> Observation

or_compose [x] = x
or_compose (x:y:z) = OrObs x (or_compose (y:z))
or_compose _ = error "or_compose applied to empty list"

choice_compose :: [Observation] -> [Contract] -> Contract

choice_compose [] [z] = z
choice_compose (ox:oy) (x:y:z) = Choice ox x (choice_compose oy (y:z))
choice_compose _ _ = error "choice_compose applied to wrong arguments"

-- specific datatypes --

data RPS = Rock | Paper | Scissors
               deriving (Eq,Ord,Show,Read)

all_rps :: [RPS]               

all_rps = [Rock, Paper, Scissors]

encoding_rps :: Num a => RPS -> a

encoding_rps Rock = 1
encoding_rps Paper = 2 
encoding_rps Scissors = 3

all_rps_enc :: [Value]

all_rps_enc = map encoding_rps all_rps

player1,player2 :: Person

player1 = 1
player2 = 2

-- encoding --

p1_hand_cv :: RPS -> Observation

p1_hand_cv = pplayed (IdentCV 1)

p2_hand_cv :: RPS -> Observation

p2_hand_cv = pplayed (IdentCV 2)

pay_p1 :: Contract -> Contract

pay_p1 c = Pay player2 player1 10 c

pay_p1_and_redeem ::  IdentCC -> IdentCC -> Contract

pay_p1_and_redeem p1 p2 = pay_p1 (redeem p1 p2) 

pay_p2 :: Contract -> Contract

pay_p2 c = Pay player1 player2 10 c 

pay_p2_and_redeem ::  IdentCC -> IdentCC -> Contract

pay_p2_and_redeem p1 p2 = pay_p2 (redeem p1 p2) 

-- reward system --

pplayed :: IdentCV -> RPS -> Observation

pplayed ident x = (CVRevealedAs ident (encoding_rps x))

victories :: [(RPS, RPS)]

victories = [(Paper, Rock), (Scissors, Paper), (Rock, Scissors)]

pp_victory :: IdentCV -> IdentCV -> Observation

pp_victory winner loser =
     or_compose [AndObs (pplayed winner x) (pplayed loser y)
                 | (x, y) <- victories]

redeem :: IdentCC -> IdentCC -> Contract

redeem p1 p2 = Both (RedeemCC p1 Null) (RedeemCC p2 Null)

rps_dist :: IdentCV -> IdentCV -> IdentCC -> IdentCC -> Contract

rps_dist v1 v2 p1 p2 = choice_compose [pp_victory v1 v2, pp_victory v2 v1]
                                      [f p1 p2 | f <- [pay_p1_and_redeem,
                                                       pay_p2_and_redeem,
                                                       redeem]]

-- seesaw --

reveal_p2 :: IdentCV -> IdentCV -> IdentCC -> IdentCC -> Contract

reveal_p2 v1 v2 p1 p2 = RevealCV v2 (check_timeout 20 (pay_p2 (rps_dist v1 v2 p1 p2)))

-- we would need a timeout here, otherwise Player 1 can wait to the last second

reveal_p1 :: IdentCV -> IdentCV -> IdentCC -> IdentCC -> Contract

reveal_p1 v1 v2 p1 p2 = RevealCV v1 (check_timeout 10 (pay_p1 (reveal_p2 v1 v2 p1 p2)))

-- value commitment --

commit_p2 :: IdentCV -> IdentCV -> IdentCC -> IdentCC -> Contract

commit_p2 v1 v2 p1 p2 = CommitValue v2 player2 all_rps_enc (reveal_p1 v1 v2 p1 p2)

commit_p1 :: IdentCV -> IdentCV -> IdentCC -> IdentCC -> Contract

commit_p1 v1 v2 p1 p2 = CommitValue v1 player1 all_rps_enc (commit_p2 v1 v2 p1 p2)

-- payment commitment --

deposit_p2 :: IdentCV -> IdentCV -> IdentCC -> IdentCC -> Contract

deposit_p2 v1 v2 p1 p2 =
     CommitCash p2 player2 20 timeout (commit_p1 v1 v2 p1 p2)

deposit_p1 :: IdentCV -> IdentCV -> IdentCC -> IdentCC -> Contract

deposit_p1 v1 v2 p1 p2 =
     CommitCash p1 player1 20 timeout (deposit_p2 v1 v2 p1 p2)

rps :: Contract

rps = deposit_p1 (IdentCV 1) (IdentCV 2) (IdentCC 1) (IdentCC 2)

-- check timeout --

check_timeout :: BlockNumber -> Contract -> Contract
check_timeout t c = Choice (BelowTimeout t) c Null

 -- Testing the semantics function

test_commits1 :: Commits

test_commits1 = Commits
                    (Set.fromList [CV (IdentCV 1) (player1),
                                   CV (IdentCV 2) (player2)])
                    (Set.fromList [CC (IdentCC 1) (player1) 20 timeout,
                                   CC (IdentCC 2) (player2) 20 timeout])
                    (Map.fromList [(IdentCV 1, encoding_rps Rock),
                                   (IdentCV 2, encoding_rps Paper)])
                    Set.empty

start_state1 :: State

start_state1 = (Map.empty, Map.empty)

test1 :: [AS]

test1 = driver start_state1 rps (input_stream test_commits1)

