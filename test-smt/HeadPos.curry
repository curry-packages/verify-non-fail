headpos :: [Int] -> Bool
headpos (x:xs) | x > 0 = True

--headpos'nonfail :: [Int] -> Bool
--headpos'nonfail xs = case xs of [] -> False
--                                y:ys -> y>0

