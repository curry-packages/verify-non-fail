
nth :: [a] -> Int -> a
nth (x:xs) n | n == 0 = x

nth'nonfail :: [a] -> Int -> Bool
nth'nonfail _  n = n == 0 -- wrong non-fail condition
