-- Example for using division on floats which requires that the second
-- argument must be non-zero.

divZero :: Float -> Float
divZero n = n / 0.0

div10 :: Float -> Float
div10 n = n / 10

div10f :: Float -> Float
div10f n = n / 10.0

div1 :: Float -> Float -> Float
div1 x y = x / y

div2 :: Float -> Float -> Float
div2 x y | y == 0    = x
         | otherwise = div1 x y

div3 :: Float -> Float -> Float
div3 x y | y == 0  = x
         | y /= 0  = div1 x y

{-

Inferred non-fail conditions:

div1'nonfail :: Float -> Float -> Bool
div1'nonfail v1 v2 = not (v2 == 0.0)

-}
