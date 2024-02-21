len :: [a] -> Int
len []     = 0
len (_:xs) = 1 + len xs

--- Returns prefix of length n.
tak :: Int -> [a] -> [a]
tak n l = if n <= 0 then [] else takep n l
 where takep _ []     = []
       takep m (x:xs) = x : tak (m - 1) xs

nth :: [a] -> Int -> a
nth (x:xs) n | n == 0 = x
             | n > 0  = nth xs (n - 1)

nth'nonfail :: [a] -> Int -> Bool
nth'nonfail xs n = n >= 0 && len (tak (n+1) xs) == n+1
-- Alternative non-fail condition, works only for finite lists:
--nth'nonfail xs n = n >= 0 && len xs > n

{-

Inferred non-fail condition when the explicitly state condition is not givens:

nth'nonfail :: [a] -> Int -> Bool
nth'nonfail v1 v2 =
  ((not (null v1)) &&
   (case v1 of
      v3 : v4 -> (v2 == 0) || (not (v2 > 0))
      _ -> True)) &&
   ((not (null v1)) &&
    (case v1 of
      v3 : v4 -> (v2 == 0) || (v2 > 0)
      _ -> True))

This is equivalent to:

nth'nonfail :: [a] -> Int -> Bool
nth'nonfail v1 v2 = not (null v1) && v2 == 0

This is correct but too restrictive.
Hence, providing the less restrictive non-fail condition is useful.

-}
