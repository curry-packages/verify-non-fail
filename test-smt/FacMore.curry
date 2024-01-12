
fac :: Int -> Int
fac n | n == 0 = 1
      | n > 0  = n * fac (n - 1)

fac5 :: Int -> Int -> Int
fac5 x n = fac (n+5)

facNeg n | n>0 = fac n
         | otherwise = gt3 n

gt3 :: Int -> Int
gt3 n | n>3 = n
