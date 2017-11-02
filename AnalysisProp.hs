module AnalysisProp where

import Analysis
import Test.QuickCheck

group :: [Maybe Int] -> Domain
group (a:t) = group_aux (a, a) t
group [] = []

group_aux :: Interval -> [Maybe Int] -> Domain
group_aux (a, b) [] = [(a, b)]
group_aux (a, Nothing) (h:t) = group_aux (a, h) t
group_aux (a, Just b) ((Just h):t)
  | b + 1 == h = group_aux (a, Just h) t
  | otherwise = (a, Just b):(group_aux (Just h, Just h) t)
group_aux (a, Just _) ([Nothing]) = [(a, Nothing)]
group_aux (_, Just _) ((Nothing):_:_) = error "Wrong list in group_aux"

split_one :: Interval -> Gen Domain 
split_one (Nothing, Nothing) = do x <- choose (-20, 19)
                                  return [(Nothing, Just x), (Just (x + 1), Nothing)]
split_one (Nothing, Just y) = do x <- choose (y - 20, y - 1)
                                 return [(Nothing, Just x), (Just (x + 1), Just y)]
split_one (Just y, Nothing) = do x <- choose (y, y + 20)
                                 return [(Just y, Just x), (Just (x + 1), Nothing)]
split_one (Just a, Just b)
  | a == b = return [(Just a, Just b)]
  | otherwise = do x <- choose (a, b - 1)
                   return [(Just a, Just x), (Just (x + 1), Just b)] 
 
split_once :: Domain -> Gen Domain
split_once g
 | length g == 0 = return g
 | otherwise = do y <- choose (0, length g - 1)
                  let (bef, (x:aft)) = splitAt y g
                  nx <- split_one x
                  return $ bef ++ nx ++ aft

split_int :: Int -> Domain -> Gen Domain
split_int st g
 | st == 0 = return g
 | st > length g = return g
 | otherwise = do ng <- split_once g
                  split_int (st - 1) ng

arbitrary_domain :: Int -> Gen Domain
arbitrary_domain s =
  do x <- sublistOf ([Nothing] ++ [Just x | x <- [-s..s]] ++ [Nothing])
     let g = group x
     st <- choose (0, s `div` 4)
     r <- split_int st g
     return $ r

arbitrary_domain_siz :: Gen Domain
arbitrary_domain_siz = sized (\s -> arbitrary_domain s)

{--------------
 - Properties -
 --------------}

all_dom_are_correct :: Property
all_dom_are_correct = forAll (arbitrary_domain_siz)
                        (\dom -> (dom /= []) ==> (
                                 all (id)
                                   [(possible x) && (possible y) && (l ||>| u)
                                    | (x@(_, u), y@(l, _)) <- zip (init dom) (tail dom)]))

intersect_correct :: Property
intersect_correct = forAll (arbitrary_domain_siz)
                      (\dom1 ->
                        forAll (arbitrary_domain_siz)
                         (\dom2 ->
                           forAll (choose (-30, 30))
                             (\x -> (((is_element x dom1) && (is_element x dom2))
                                      == (is_element x (intersect_dom dom1 dom2))))))

ij :: Maybe Int -> Domain -> Bool
ij Nothing _ = True
ij (Just x) d = is_element x d

check_result_interv :: Domain -> Domain -> Domain -> Int -> Property
check_result_interv dom1 dom2 w x =
  if ied1 then (if ied2 then whenFail (putStrLn "Intersection!") iedw
                        else ((whenFail (putStrLn "Next valid element!")
                                        (ij (next_valid_element x dom2) w))
                               .&&.
                              (whenFail (putStrLn "Next valid element middle!")
                                        ((next_valid_element x dom2) ===
                                         (next_valid_element x w)))))
  else (if iedw then ((whenFail (putStrLn "Not on right side!") ied2)
                        .&&.
                      (whenFail (putStrLn "Previous also valid!")
                                (not $ is_element (x - 1) dom2))
                        .&&.
                      (whenFail (putStrLn "Not smaller first element!")
                                (case dom1 of
                                  [] -> False
                                  ((a,_):_) -> (Just x) |>|| a)))
                else (whenFail (putStrLn "True failed!!!") True))
  where ied1 = ie dom1
        ied2 = ie dom2
        iedw = ie w
        ie = is_element x

wait_interv_correct :: Property
wait_interv_correct = forAll (arbitrary_domain_siz)
                        (\dom1 ->
                          forAll (arbitrary_domain_siz)
                           (\dom2 ->
                             forAll (choose (-30, 30))
                               (\x -> check_result_interv dom1 dom2
                                              (wait_interval dom1 dom2) x)))



