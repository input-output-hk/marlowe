module EqSolve(solveLEInt) where

import Data.Maybe (listToMaybe, isJust, catMaybes)
import Data.List (genericIndex, transpose, sortOn, genericTake, genericDrop, genericLength, nub)

normaliseFirst :: [[Rational]] -> [[Rational]]
normaliseFirst [] = []
normaliseFirst l@([]:_) = l
normaliseFirst ((x:t1):t2) =
  ((1:st1):(simplify t2 st1))
  where st1 = map (/ x) t1

simplify :: [[Rational]] -> [Rational] -> [[Rational]]
simplify [] _ = []
simplify ((y:t1):t2) l = ((0:(zipWith (+) t1 (map (* (-y)) l))):(simplify t2 l))

sortRowsByLeadingZeroes :: ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
sortRowsByLeadingZeroes (m, r, c) = (nm, nr, c)
  where
    (nm, nr) = unzip $ sortOn (length . (takeWhile (== 0)). fst) $ zip m r

pullZeroColumnsAux :: [([Rational], b)] -> [([Rational], b)] -> [([Rational], b)]
pullZeroColumnsAux acc [] = reverse acc
pullZeroColumnsAux acc [h] = (reverse (h:acc))
pullZeroColumnsAux acc (c@(l, _):t)
  | all (== 0) l = (c:(pullZeroColumnsAux acc t))
  | otherwise = pullZeroColumnsAux (c:acc) t

pullZeroColumns :: ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
pullZeroColumns (m, r, c) = (transpose tm, r, nc)
  where
    (tm, nc) = unzip $ pullZeroColumnsAux [] $ zip (transpose m) c

{-separateLastColumn :: ([[Rational]], [a], [b]) -> (([Rational], b), ([[Rational]], [a], [b]))
separateLastColumn (m, r, c) = ((map last m, last c), (map init m, r, init c))

restoreLastColumn :: ([Rational], b) -> ([[Rational]], [a], [b])) -> ([[Rational]], [a], [b]))
restoreLastColumn (lm, lc) (m, r, c) = (zipWith (\x y -> x ++ [y]) m lm, r, c ++ [lc])-}

separateEmptyColumnsAux :: ([[Rational]], [a], [b]) -> ([[Rational]], [b]) -> (([[Rational]], [b]), ([[Rational]], [a], [b]))
separateEmptyColumnsAux l@(_, _, []) acc = (acc, l)
separateEmptyColumnsAux l@(m, r, (ch:ct)) acc@(accm, accc)
 | all ((== 0) . head) m = separateEmptyColumnsAux ((map tail m), r, ct) (((map head m):accm), ch:accc)
 | otherwise = (acc, l)

separateEmptyColumns :: ([[Rational]], [a], [b]) -> (([[Rational]], [b]), ([[Rational]], [a], [b]))
separateEmptyColumns l = separateEmptyColumnsAux l ([], [])

restoreEmptyColumns :: ([[Rational]], [b]) -> ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
restoreEmptyColumns ([], []) i = i
restoreEmptyColumns (h:t, h2:t2) (m, r, c) = restoreEmptyColumns (t, t2) ((zipWith (:) h m), r, h2:c)
restoreEmptyColumns _ _ = error "Inconsistent width of matrix"

separateTopLeft :: ([[Rational]], [a], [b]) -> (Maybe ([Rational], [Rational], a, b), ([[Rational]], [a], [b]))
separateTopLeft (h:t, hr:tr, hc:tc) = (Just (h, map head t, hr, hc), (map tail t, tr, tc))
separateTopLeft c = (Nothing, c)

restoreTopLeft :: Maybe ([Rational], [Rational], a, b) -> ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
restoreTopLeft (Just (h, ch, hr, hc)) (t, tr, tc) = (h:(zipWith (:) ch t), hr:tr, hc:tc)
restoreTopLeft Nothing c = c 

emptyLowerDiag :: ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
emptyLowerDiag (m, [], c) = (m, [], c)
emptyLowerDiag i = restoreEmptyColumns e3 $ restoreTopLeft e4 $ if (isJust e4) then emptyLowerDiag i4 else i4
  where
    i2 = sortRowsByLeadingZeroes i
    (e3, (m, r, c)) = separateEmptyColumns i2
    nm = normaliseFirst m 
    (e4, i4) = separateTopLeft (nm, r, c)

emptyLowerDiagNoSort :: ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
emptyLowerDiagNoSort (m, [], c) = (m, [], c)
emptyLowerDiagNoSort (m, r, c) = restoreTopLeft e4 $ if (isJust e4) then emptyLowerDiagNoSort i4 else i4
  where
    nm = normaliseFirst m 
    (e4, i4) = separateTopLeft (nm, r, c)

hasOneSolAux :: Integer -> [[Rational]] -> Bool
hasOneSolAux i [] = True
hasOneSolAux i (h:t)
  | (genericLength h > i + 1) && (all (== 0) (genericTake i h)) && ((head (genericDrop i h)) == 1) = hasOneSolAux (i + 1) t
  | otherwise = False

hasOneSol :: ([[Rational]], [a], [b]) -> Bool
hasOneSol (m, _, _) = hasOneSolAux 0 m

almostReverse :: [a] -> [a]
almostReverse l@(_:_) = (reverse (init l)) ++ [last l]
almostReverse [] = []

flipMatrix :: ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
flipMatrix (m, r, c) = (map almostReverse $ reverse m, almostReverse r, almostReverse c)

emptyUpperDiag :: ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
emptyUpperDiag = flipMatrix . emptyLowerDiagNoSort . flipMatrix 

solveExactSystem :: ([[Rational]], [a], [b]) -> Maybe [(b, Rational)]
solveExactSystem m
 | hasOneSol echelon = Just $ zip fc $ map last $ fm
 | otherwise = Nothing
  where echelon = emptyLowerDiag m
        solved@(fm, _, fc) = emptyUpperDiag echelon

removeLinearDependent :: ([[Rational]], [a], [b]) -> ([[Rational]], [a], [b])
removeLinearDependent m = (mf, rf, cf)
  where (m2, r, cf) = emptyLowerDiag m
        mf = takeWhile (not . (all (== 0))) m2
        rf = take (length mf) r

combinations :: Integer -> [a] -> [[a]]
combinations i [] = if (i == 0) then [[]] else []
combinations i l@(h:t)
 | genericLength l < i = []
 | genericLength l == i = [l]
 | otherwise = combinations i t ++ [(h:x) | x <- combinations (i - 1) t]

combinationsEq :: ([[Rational]], [a], [b]) -> [([[Rational]], [a], [b])]
combinationsEq ([], [], []) = [([], [], [])]
combinationsEq (m, r, c) = [ let (nm, nr) = unzip oc in (nm, nr, c) | oc <- co ]
  where
    co = combinations ((genericLength c) - 1) $ zip m r

checkSolutionLE :: Eq b => ([[Rational]], [a], [b]) -> [(b, Rational)] -> Bool
checkSolutionLE (m, r, c) s = all (\y -> (sum $ (zipWith (*) c3) $ init y) <= last y) m
   where c3 = [(case lookup e s of
                 Just x -> x
                 Nothing -> 0) | e <- c]

makeDelta :: Integer -> Integer -> [Rational]
makeDelta d l = [ if (x == d) then 1 else 0 | x <- [0..l] ]

addAxis :: ([[Rational]], [a], [b]) -> ([[Rational]], [Either Integer a], [b])
addAxis (m, r, c) = (nm, nr, c)
  where
   lr = map (Right) r
   cl = (genericLength c) - 1
   nm = m ++ (map (`makeDelta` cl) [0..cl])
   nr = lr ++ (map (Left) [0..cl])

solveLE :: Eq b => ([[Rational]], [a], [b]) -> [[(b, Rational)]]
solveLE m = filter (checkSolutionLE m) [[(x, 0) | x <- ec] ++ sol | sol <- (catMaybes $ map solveExactSystem $ combinationsEq prunedEqs)]
  where instEqs = addAxis m
        ((_, ec), prunedEqs) = separateEmptyColumns $ pullZeroColumns $ instEqs

nonFractional :: Rational -> Bool
nonFractional d = (toRational $ ceiling d) == d

splitOrConvertSolutionAux :: [(b, Rational)] -> [(b, Integer)] -> Either (b, Rational) [(b, Integer)]
splitOrConvertSolutionAux [] l = Right l
splitOrConvertSolutionAux ((b,v):t) l
 | nonFractional v = splitOrConvertSolutionAux t ((b, (ceiling v)):l)
 | otherwise = Left (b, v)

splitOrConvertSolution :: [(b, Rational)] -> Either (b, Rational) [(b, Integer)]
splitOrConvertSolution s = splitOrConvertSolutionAux s []

genericElemIndex :: Eq a => a -> [a] -> Integer
genericElemIndex _ [] = error "Element not in list!"
genericElemIndex e (h:t)
 | e == h = 0
 | otherwise = 1 + (genericElemIndex e t)

addIE :: Integer -> Rational -> Rational -> Integer -> [Rational]
addIE p v n w = [if (x == w) then n else (if x == p then v else 0) | x <- [0..w]]

addLE :: Integer -> Rational -> Integer -> [Rational]
addLE p n w = addIE p 1 n w

addGE :: Integer -> Rational -> Integer -> [Rational]
addGE p n w = addIE p (-1) (-n) w

aimForRight :: [Either a b] -> Maybe (Either a b)
aimForRight [] = Nothing
aimForRight [Left a] = Just $ Left a
aimForRight ((Right b):_) = Just $ Right b
aimForRight (_:t) = aimForRight t

splitOrConvert :: Eq b => ([[Rational]], [a], [b]) -> [[(b, Rational)]] -> Maybe (Either [([[Rational]], [a], [b])] [(b, Integer)])
splitOrConvert (m, r, c) sol =
  case aimForRight $ map splitOrConvertSolution sol of
    Just (Left (b, n)) -> let t = toRational $ ceiling n in
                          let f = toRational $ floor n in
                          let p = genericElemIndex b c in
                          let w = genericLength r in
                          Just $ Left [(((addLE p f w):m), r, c), (((addGE p f w):m), r, c)]
    Just (Right sol) -> Just $ Right sol
    Nothing -> Nothing

solveLEIntAux :: Eq a => Eq b => [([[Rational]], [a], [b])] -> Maybe [(b, Integer)]
solveLEIntAux [] = Nothing
solveLEIntAux (h:t) =
  case splitOrConvert h rSol of
    Just (Left nh) -> solveLEIntAux (nub (t ++ nh))
    Just (Right s) -> Just s
    Nothing -> solveLEIntAux t
  where
   rSol = solveLE h

solveLEInt :: Eq a => Eq b => ([[Rational]], [a], [b]) -> Maybe [(b, Integer)]
solveLEInt m = solveLEIntAux [m]

