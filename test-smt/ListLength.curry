len :: [a] -> Int
len []     = 0
len (_:xs) = 1 + len xs

f :: [a] -> [a]
f xs | len xs < 10 = xs

--usef x = f [x] -- polymorphic
usef x = [1::Int]
--usef = f "abc"
