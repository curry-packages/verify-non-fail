-----------------------------------------------------------------------------
--- A simplifier for FlatCurry programs.
--- In particular, it replaces calls to Eq.== implementations by Prelude.==
---
--- @author  Michael Hanus
--- @version September 2024
---------------------------------------------------------------------------

module FlatCurry.Simplify
  --( simpProg, simpFuncDecl, simpExpr )
 where

import Data.List ( find, isPrefixOf )

import FlatCurry.Build
import FlatCurry.Goodies
import FlatCurry.Names
import FlatCurry.Types

----------------------------------------------------------------------------

simpProg :: Prog -> Prog
simpProg = updProgExps simpExpr

simpFuncDecl :: FuncDecl -> FuncDecl
simpFuncDecl = updFuncBody simpExpr

--- Implements the following transformations:
--- * simplify equality instance on lists
--- * simplify EQ.== calls
--- * simplify uses of otherwise:
---       case otherwise of { True -> e1 ; False -> e2 } ==> e1
--- * simplify application of `Prelude.$`:
---       f $ e ==> f e
--- * simplify `Prelude.apply` for partially applied first arguments
--- * replace `Prelude.otherwise` by `True`
simpExpr :: Expr -> Expr
simpExpr exp = case exp of
  Var  _          -> exp
  Lit  _          -> exp
  Comb ct qf args -> simpComb ct qf (map simpExpr args)
  Let  bs e       -> Let (map (\ (v,b) -> (v, simpExpr b)) bs) (simpExpr e)
  Or   e1 e2      -> Or (simpExpr e1) (simpExpr e2)
  Case ct e brs   -> if isOtherwise e
                       then simpExpr (trueBranch brs)
                       else Case ct (simpExpr e) (map simpBranch brs)
  Typed e te      -> Typed (simpExpr e) te
  Free  vs e      -> Free  vs (simpExpr e)
 where
  simpComb ct qf args
   -- simplify application of `Prelude.apply` to partially applied functions:
   | qf == pre "apply" && length args == 2
   = case head args of
       Comb (FuncPartCall n) qft1 fargs ->
            simpComb (if n==1 then FuncCall else FuncPartCall (n-1)) qft1
                     (fargs ++ [args!!1])
       _ -> moreSimpComb (Comb  ct qf args)
   -- inline application of `Prelude.$`:
   | qf == pre "$"
   = simpComb ct (pre "apply") args
   -- simplify `Prelude.otherwise`:
   | qf == pre "otherwise"
   = fcTrue
   | qf == pre "not" && length args == 1
   = fcNot (head args)
   | qf == pre "||" && length args == 2
   = fcOr (head args) (args!!1)
   | qf == pre "&&" && length args == 2
   = fcAnd (head args) (args!!1)
   -- simplify equality instance on lists:
   | ct == FuncCall && qf == pre "_impl#==#Prelude.Eq#[]#0##"
   = Comb ct (pre "==") (tail args)
   | ct == FuncCall && qf == pre "_impl#===#Prelude.Data#[]#0##"
   = Comb ct (pre "===") (tail args)
   -- simplify equal class calls:
   | otherwise
   = moreSimpComb (Comb ct qf args)

  moreSimpComb e = simpArithExp (simpClassEq e)

  simpBranch (Branch p e) = Branch p (simpExpr e)

  isOtherwise e = case e of Comb _ qf _ -> qf == pre "otherwise"
                            _           -> False

  trueBranch brs =
    maybe (error "simpExpr: Branch with True pattern does not exist!")
          (\ (Branch _ e) -> e)
          (find (\ (Branch p _) -> isTruePattern p) brs)

  isTruePattern p = case p of Pattern qf [] -> qf == pre "True"
                              _             -> False

simpClassEq :: Expr -> Expr
simpClassEq exp = case exp of
  Comb FuncCall qt1
        [Comb FuncCall qt2
          [Comb FuncCall qt3 [_], e1], e2]
   | qt1 == pre "apply" && qt2 == pre "apply" && qt3 == pre "=="
   -> Comb FuncCall (pre "==") [e1,e2]
  _ -> exp

--- Simplify applications of primitive operations, i.e.,
---     apply (apply op e1) e2      ==> op [e1,e2]
---     apply (apply op e1 :: t) e2 ==> op [e1,e2]
---     apply op e1                 ==> op [e1]
simpArithExp :: Expr -> Expr
simpArithExp exp = case exp of
  Comb FuncCall qt1 [Comb FuncCall qt2 [op, e1], e2]
   | qt1 == pre "apply" && qt2 == qt1
   -- apply (apply op e1) e2 ==> op [e1,e2]
   -> case op of Comb FuncCall qn []           -> replaceBinOp qn e1 e2
                 Typed (Comb FuncCall qn []) _ -> replaceBinOp qn e1 e2
                 _                             -> exp
  Comb FuncCall qt1 [Typed (Comb FuncCall qt2 [op, e1]) _, e2]
   | qt1 == pre "apply" && qt2 == qt1
   -- apply (apply op e1 :: type) e2 ==> op [e1,e2]
   -> case op of Comb FuncCall qn []           -> replaceBinOp qn e1 e2
                 Typed (Comb FuncCall qn []) _ -> replaceBinOp qn e1 e2
                 _                             -> exp
  Comb FuncCall qt1 [op, e1] | qt1 == pre "apply" -- apply op e1 ==> op [e1]
    -> case op of Comb FuncCall qn []           -> replaceUnOp qn e1
                  Typed (Comb FuncCall qn []) _ -> replaceUnOp qn e1
                  _                             -> exp
  Comb FuncCall qn [e1,e2] -> replaceBinOp qn e1 e2
  Comb FuncCall qn [e1]    -> replaceUnOp qn e1
  _                        -> exp
 where
  replaceBinOp (mn,fn) e1 e2
    | mn == "Prelude" = maybe exp
                              (\fp -> Comb FuncCall (mn,fp) [e1,e2])
                              (lookup fn binaryPrimOps)
    | otherwise       = exp

  replaceUnOp (mn,fn) e1
    | mn == "Prelude" = maybe exp
                              (\fp -> Comb FuncCall (mn,fp) [e1])
                              (lookup fn unaryPrimOps)
    | otherwise       = exp

------------------------------------------------------------------------------
