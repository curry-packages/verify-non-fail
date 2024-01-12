len :: [a] -> Int
len []     = 0
len (_:xs) = 1 + len xs

--f :: [Int] -> [Int]
f xs | len xs < 10 = xs

usef x = f [x] --[1::Int]
--usef = f "abc"
