module FlatCurry.NormalizeLet ( normalizeLet ) where

import Data.SCC          ( scc )
import FlatCurry.Goodies ( allVars )
import FlatCurry.Types

--- Normalize all let expressions occurring in an expression
--- by transforming each let expression into a hierarchical let expression
--- according to the dependencies of the bindings.
--- For instance,
---
---     let { x = f y ; y = g z} in e
---
--- is transformed into
---
---     let { y = g z} in let { x = f y} in e
---
normalizeLet :: Expr -> Expr
normalizeLet exp = case exp of
  Var _         -> exp
  Lit _         -> exp
  Comb ct qf es -> Comb ct qf (map normalizeLet es)
  Let bs e      -> foldr Let e (sortLetBindings bs)
  Free vs e     -> Free vs (normalizeLet e)
  Or e1 e2      -> Or (normalizeLet e1) (normalizeLet e2)
  Case ct be bs -> Case ct (normalizeLet be)
                        (map (\ (Branch p e) -> Branch p (normalizeLet e)) bs)
  Typed e t     -> Typed (normalizeLet e) t

-- Sort a list of let bindings into strongly connected compontents
-- sorted by the dependencies of the defined variables.
sortLetBindings :: [(Int,TypeExpr,Expr)] -> [[(Int,TypeExpr,Expr)]]
sortLetBindings bs = scc definedBy usedIn bs
 where
  definedBy (v,_,_) = [v]

  usedIn (_,_,e) = filter (`elem` varsOfLetBind bs) (allVars e)
