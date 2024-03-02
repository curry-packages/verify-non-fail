-- Examples with encapsulated search via set functions

import Control.Search.SetFunctions

head :: [a] -> a
head (x:_) = x

-- This operation encapsulates the failure of head but not of its argument:
hasHead :: [Int] -> Bool
hasHead xs = not (isEmpty ((set1 head) xs))

-- This operation has `{:}` as a call type:
headHasHead :: [[Int]] -> Bool
headHasHead xs = hasHead (head xs)
