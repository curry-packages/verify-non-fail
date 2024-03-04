len :: [a] -> Int
len []     = 0
len (_:xs) = 1 + len xs

f :: [a] -> [a]
f xs | len xs < 10 = xs

usefPoly x = f [x] -- polymorphic

usefInt x = f [1::Int]

usefChar = f "abc"
