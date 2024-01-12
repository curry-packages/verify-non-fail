-----------------------------------------------------------------------------
--- Auxiliaries to build FlatCurry expressions.
---
--- @author  Michael Hanus
--- @version December 2023
---------------------------------------------------------------------------

module FlatCurry.Build
  --( fcTrue, fcFalse, fcNot, fcOr, fcAnd, fcAnds )
 where

import FlatCurry.Types

------------------------------------------------------------------------------

fcTrue :: Expr
fcTrue = Comb ConsCall (pre "True") []

fcFalse :: Expr
fcFalse = Comb ConsCall (pre "False") []

fcNot :: Expr -> Expr
fcNot e = case e of
  Comb ConsCall qf []      | qf == pre "False" -> fcTrue
                           | qf == pre "True"  -> fcFalse
  Comb FuncCall qf [e1]    | qf == pre "not"   -> e1
  Comb FuncCall qf [e1,e2] | qf == pre "&&"    -> fcOr  (fcNot e1) (fcNot e2)
                           | qf == pre "||"    -> fcAnd (fcNot e1) (fcNot e2)
  Case ct ce brs -> Case ct ce (map (\(Branch p be) -> Branch p (fcNot be)) brs)
  _                                            -> Comb FuncCall (pre "not") [e]

-- Disjunction of two expressions.
fcOr :: Expr -> Expr -> Expr
fcOr e1 e2 | e1 == fcFalse = e2
           | e2 == fcFalse = e1
           | e1 == fcTrue  = fcTrue
           | e2 == fcTrue  = fcTrue
           | otherwise     = Comb FuncCall (pre "||") [e1,e2]

-- Conjunction of two expressions.
fcAnd :: Expr -> Expr -> Expr
fcAnd e1 e2 | e1 == fcTrue  = e2
            | e2 == fcTrue  = e1
            | e1 == fcFalse = fcFalse
            | e2 == fcFalse = fcFalse
            | otherwise     = Comb FuncCall (pre "&&") [e1,e2]

-- Conjunction of a list of expressions.
fcAnds :: [Expr] -> Expr
fcAnds = foldr fcAnd fcTrue

-- Equality between two expressions.
fcEqu :: Expr -> Expr -> Expr
fcEqu e1 e2 = Comb FuncCall (pre "==") [e1,e2]

----------------------------------------------------------------------------

pre :: String -> QName
pre f = ("Prelude",f)

----------------------------------------------------------------------------
