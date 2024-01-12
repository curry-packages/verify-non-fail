div1 :: Int -> Int -> Int
div1 x y = div x y

div2 :: Int -> Int -> Int
div2 x y | y == 0    = x
         | otherwise = div1 x y

div3 :: Int -> Int -> Int
div3 x y | y == 0  = x
         | y /= 0  = div1 x y

{-

Inferred non-fail conditions:

div1'nonfail :: Int -> Int -> Bool
div1'nonfail v1 v2 = v2 /= 0

-}
