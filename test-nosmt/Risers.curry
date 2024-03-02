-- Example taken from:
-- 
-- N. Mitchell, C. Runciman:
-- A Static Checker for Safe Pattern Matching in Haskell
-- Trends in Functional Programming, Vol. 6, pages 15-30, 2007

risers :: Ord a => [a] -> [[a]]
risers []        = []
risers [x]       = [[x]]
risers (x:y:etc) = if x <= y then (x:s):ss else [x]:(s:ss)
 where
  (s:ss) = risers (y:etc)

-- Flat version:
risersF xs =
  case xs of [] -> []
             [x] -> [[x]]
             (x:y:etc) -> risers2 (x <= y) x (risersF (y:etc))

risers2 b x y = case y of
                  (s:ss) -> case b of
                               True  -> (x:s) : ss
                               False -> [x] : (s:ss)
