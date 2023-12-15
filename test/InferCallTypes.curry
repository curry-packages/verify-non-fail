-- Example program to demonstrate the inference of call types
-- due to calling other call-type restricted operations.

isTrue True = True

trueTrue True True = True

trueFalse True False = True

g x = isTrue x

h x = trueTrue x x

k x y = trueTrue x y

j1 x = trueFalse x x
j2 x y = trueFalse x y
j3 x y = j2 x y

maxList :: Ord a => [a] -> a
maxList xs =  foldl1 max xs
