-- Examples for using the operation sqrt, allowed only on non-negative numbers:

sqrtP2 :: Float -> Float
sqrtP2 x = sqrt (x+2)
{-
-- Generated non-fail condition:
sqrtP2'nonfail :: Float -> Bool
sqrtP2'nonfail v1 = (v1 + 2.0) >= 0.0
-}

-- This use is ok.
three :: Float
three = sqrt 9.0

-- This is always failing.
failedSqrt :: Float
failedSqrt = sqrt (-2.0)

-- This use of sqrt is always ok.
sqrtOrZero :: Float -> Float
sqrtOrZero x = if x >= 0 then sqrt x
                         else 0.0
