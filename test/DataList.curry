--- Returns the last element of a non-empty list.
last :: [a] -> a
last [x]            = x
last (_ : xs@(_:_)) = last xs

useLast = [True,False]

--- Returns the input list with the last element removed.
init :: [a] -> [a]
init [_]          = []
init (x:xs@(_:_)) = x : init xs


myhead (x:xs) = x
mytail (x:xs) = xs

aBool = False ? True

split :: (a -> Bool) -> [a] -> [[a]]
split _ [] = [[]]
split p (x:xs) =
 if aBool then [] : split p xs
          else let sp = split p xs
               in (x : myhead sp) : mytail sp
