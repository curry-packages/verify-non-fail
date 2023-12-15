-- Examples with encapsulated search

import Control.Search.Unsafe

-- Call type: {:}
head :: [a] -> a
head (x:_) = x

-- Call type: {:}
hd :: [a] -> a
hd xs = head xs

-- Call type: FAILING since restriction on argument is not possible
hdfree :: [Bool] -> Bool
hdfree _ = let ys free in head ys

-- Call type ANY due to encpsaulation of possible failures
allHeads :: [Bool] -> [Bool]
allHeads xs = allValues (head xs)

-- Call type ANY due to encpsaulation of possible failures
oneHead :: [Bool] -> Maybe Bool
oneHead xs = oneValue (head xs)
