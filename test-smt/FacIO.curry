-- Factorial function fails on negative numbers:
fac :: Int -> Int
fac n | n == 0 = 1
      | n > 0  = n * fac (n - 1)

-- Reads a number and call `fac` after checking it:
facIO :: IO ()
facIO = do
  putStr "Input some non-negative integer: "
  s <- getLine
  case readInt s of
    --[(n,_)] -> if n >= 0 then print (fac n) else facIO
    Just n   -> if n >= 0 then print (fac n) else facIO
    _       -> facIO

-- Dummy definition:
reads :: String -> [(Int,String)]
reads _ = [(0,"")]

readInt :: String -> Maybe Int
readInt _ = Just 10
