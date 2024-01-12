sig :: Int -> Int
sig x | x>0  = 1
      | x==0 = 0
      | x<0  = -1

abs :: Int -> Int
abs x | x >= 0 = x
      | x <  0 = 0 - x
