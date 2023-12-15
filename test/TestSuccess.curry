-- Test for operations that should be successfully verified.

id :: a -> a
id x = x

-- Booleans

myTrue = True

myBool = False ? True

myNot False = True
myNot True  = False

solve True = True

solveMyTrue = solve myTrue

andp False _ = False
andp True True = True
andp True False = False

andp2 = andp myBool myBool


-- Lists (structured data)

myhead (x:xs) = x

null []    = True
null (_:_) = False

f xs = case null xs of
         True -> True
         False -> myhead xs

-- Base types and literals

k 0 = 'a'
k 1 = 'b'

j = k (0?1)

-- Example for unreachable branches


unreachBranch x =
  case x of True -> case x of False -> solve x
                              True  -> solve x
