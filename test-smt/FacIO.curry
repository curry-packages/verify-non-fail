-- Factorial function fails on negative numbers:
fac :: Int -> Int
fac n | n == 0 = 1
      | n > 0  = n * fac (n - 1)

-- Reads a number and call `fac` after checking it:
facIO :: IO ()
facIO = do
  putStr "Input some non-negative integer: "
  mbn <- fmap readInt getLine
  case mbn of Just n | n >= 0 -> print (fac n)
              _               -> facIO

-- Reads an integer from a string.
readInt :: String -> Maybe Int
readInt s = case reads s of [(n,"")] -> Just n
                            _        -> Nothing
