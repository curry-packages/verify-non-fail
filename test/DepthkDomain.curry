
-- This case on literals cannot be verified with the top-level cons domain
-- since the abstract call type is empty.
-- With a depth-k domain and k>1, it can be represented.
just01 (Just 0) = 'a'
just01 (Just 1) = 'b'

-- Similarly, this pattern also requires a refined domain:
falseTail (False:xs) = xs

mainFT = falseTail [False,True]
