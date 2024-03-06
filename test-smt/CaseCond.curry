-- Example for a condition related to some part of a pattern.

pos :: Int -> Int
pos n | n > 0 = n

sumPos :: (Int,Int) -> Int
sumPos (x,y) = x + pos y
