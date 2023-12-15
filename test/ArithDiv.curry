-- Some tests for arithmetic operations, in particular, division operations.

-- This operation is not failing:
f :: Int
f = 3*4

-- This operation might fail due to the integer division:
g :: Int -> Int
g x = 3 `div` x

-- ...but this operation does not fail since the divisor is non-zero:
even :: Int -> Bool
even n = (n `mod` 2) == 0
