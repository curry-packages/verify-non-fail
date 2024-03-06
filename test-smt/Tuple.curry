-- Example to test verification with user-defined types and tuples.

{-# LANGUAGE NoDataDeriving #-}

data Pair a b = MkPair a b

fPair :: Pair Int Int -> Bool
fPair (MkPair x y) | x+y > 0 = True

usePair :: Int -> Bool
usePair x | x>0 = fPair (MkPair x x)


fTriple :: (Int,Int,Int) -> Bool
fTriple (x,y,z) | x+y+z > 0 = True

useTriple :: Int -> Bool
useTriple x | x>0 = fTriple (x,x,x)
