module IStack(IStack, empty, insert, IStack.lookup, pop) where

import qualified Data.Map as Map

data IStack k v = IStack (Map.Map k [v])
   deriving (Eq,Ord,Show,Read)

empty :: IStack k v
empty = IStack $ Map.empty

insert :: Ord k => k -> v -> IStack k v -> IStack k v
insert k v (IStack m)
 = case Map.lookup k m of
     Just l -> IStack $ Map.insert k (v:l) m
     Nothing -> IStack $ Map.insert k [v] m

lookup :: Ord k => k -> IStack k v -> Maybe v
lookup k (IStack m)
 = case Map.lookup k m of
    Just [] -> error "IStack is corrupt!"
    Just (h:_) -> Just h
    Nothing -> Nothing

pop :: Ord k => k -> IStack k v -> IStack k v
pop k i@(IStack m)
 = case Map.lookup k m of
     Just [] -> error "IStack is corrupt!"
     Just [_] -> (IStack $ Map.delete k m)
     Just (_:t) -> (IStack $ Map.insert k t m)
     Nothing -> i
