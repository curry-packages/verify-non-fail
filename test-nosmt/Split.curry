{-
myhead (x:xs) = x
mytail (x:xs) = xs

aBool = False?True

split :: (a -> Bool) -> [a] -> [[a]]
split _ [] = [[]]
split p (x:xs) =
 if aBool then [] : split p xs
          else let sp = split p xs
               in (x : myhead sp) : mytail sp
-}

split :: (a -> Bool) -> [a] -> [[a]]
split _ []     = [[]]
split p (x:xs) | p x       = [] : split p xs
               | otherwise = let (ys:yss) = split p xs in (x:ys):yss

