module TreeAnalysis where

import Analysis
import Semantics
import TreeVisualise
import qualified Data.Map as Map
import qualified Data.List as List

-----------------------
-- Tree construction --
-----------------------

type ATran = Maybe Event 
type ANode = (Domain, [Action])

data Acc = Acc {
                 node_info :: Map.Map Int AnalysisState,
                 node_info_rev :: Map.Map AnalysisState Int,
                 transitions :: [(Int, Int, ATran)],
                 nodes :: [(Int, ANode)],
                 last_node_id :: Int
               }
           deriving (Eq,Ord,Show,Read)

list_to_maybe :: [a] -> Maybe a
list_to_maybe [] = Nothing
list_to_maybe [x] = Just x
list_to_maybe _ = error "Several elements in list_to_maybe!"

get_tree_aux :: [(Int, AnalysisState)] -> Acc -> Acc
get_tree_aux [] acc = acc
get_tree_aux ((parent, curr_as):t) (acc@(Acc {transitions = tra,
                                              nodes = nods,
                                              node_info = ni,
                                              node_info_rev = nirev,
                                              last_node_id = lnid}))
  | is_rep curr_as = get_tree_aux t acc
  | List.null diff && List.null diff_act =
                        get_tree_aux ([(parent, new_as)
                                       | new_as <- (analysis_step [curr_as]),
                                         not $ is_rep new_as] ++ t) new_acc
  | otherwise = get_tree_aux ((new_node_id, curr_as):t) new_node_acc
  where curr_eve = get_events curr_as
        past_eve = get_events (Map.findWithDefault err parent $ node_info acc)
        diff = curr_eve List.\\ past_eve
        curr_act = get_actions curr_as
        past_act = get_actions (Map.findWithDefault err parent $ node_info acc)
        diff_act = curr_act List.\\ past_act
        err = (error "Parent does not exist in get_tree_aux!")
        is_rep x = Map.member x nirev 
        new_node_acc = acc {last_node_id = new_node_id,
                            transitions = ((parent, new_node_id, list_to_maybe diff):tra),
                            nodes = ((new_node_id, (possible_block curr_as,
                                                    diff_act)):nods),
                            node_info = Map.insert new_node_id curr_as ni}
        new_acc = acc {node_info_rev = Map.insert curr_as new_node_id nirev}
        new_node_id = lnid + 1

tran_show :: ATran -> String
tran_show Nothing = ""
tran_show (Just x) = show x

get_tree :: Contract -> Acc
get_tree c = get_tree_aux [(initial_st, initial_as)]
                          Acc {
                                node_info = Map.singleton initial_st initial_as,
                                node_info_rev = Map.empty,
                                transitions = [],
                                nodes = [(initial_st, (possible_block initial_as, []))],
                                last_node_id = initial_st
                              }
  where initial_st = 0
        initial_as = empty_analysis_state c

show_sidel :: Maybe Int -> String
show_sidel Nothing = "-∞"
show_sidel (Just x) = (show x)

show_side :: Maybe Int -> String
show_side Nothing = "∞"
show_side (Just x) = (show x)

show_sing_domain :: Domain -> String
show_sing_domain [(a, b)] = show_sidel a ++ " to " ++ show_side b
show_sing_domain _ = error "Domain is complex in show_sing_domain!"

acc_to_gd :: Acc -> GraphData
acc_to_gd acc = (List.nub $ map (\(x, (d, y)) -> (x, List.concat
                                                  $ List.intersperse "\n"
                                                  $ ((show_sing_domain d):(map (show) y))))
                          $ nodes acc,
                 List.nub $ map (\(x, y, z) -> (x, y, tran_show z)) $ transitions acc)

visualise_tree :: Contract -> IO ()
visualise_tree c = visualise $ acc_to_gd $ get_tree c

