nth :: [a] -> Int -> a
nth (x:xs) n | n == 0 = x
             | n > 0  = nth xs (n - 1)

{-

Inferred non-fail condition when the explicitly state condition is not givens:

nth'nonfail :: [a] -> Int -> Bool
nth'nonfail v1 v2 =
  ((not (null v1)) &&
   (not (case v1 of
           v3 : v4 -> (not (v2 == 0)) && (v2 > 0)
           _ -> False))) &&
  ((not (null v1)) &&
   (not (case v1 of
           v3 : v4 -> (not (v2 == 0)) && (not (v2 > 0))
          _ -> False)))

This is equivalent to:

nth'nonfail :: [a] -> Int -> Bool
nth'nonfail v1 v2 = not (null v1) && v2 == 0

This is correct but too restrictive.
Hence, providing the less restrictive non-fail condition is useful.

-}
