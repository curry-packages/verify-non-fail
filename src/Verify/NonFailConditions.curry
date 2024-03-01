-----------------------------------------------------------------------------
--- Definition and some operations for non-fail conditions.
---
--- @author  Michael Hanus
--- @version January 2024
---------------------------------------------------------------------------

module Verify.NonFailConditions
 where

import Data.List         ( (\\), find, isPrefixOf, isSuffixOf, nub
                         , splitOn, union )

import Contract.Names    ( encodeContractName )
import FlatCurry.Goodies
import FlatCurry.Types

import FlatCurry.Build
import FlatCurry.Print
import FlatCurry.Simplify

--- Non-fail conditions are represented as a pair of typed variables
--- occurring in the conditions and a Boolean expressions
--- (in FlatCurry representation).
type NonFailCond = ([(Int,TypeExpr)], Expr)

--- The always unsatisfiable non-fail condition.
nfcFalse :: NonFailCond
nfcFalse = ([],fcFalse)

--- Generate a non-fail condition from a list of variables types
--- and a list of Boolean expressions.
genNonFailCond :: [(Int,TypeExpr)] -> Expr -> NonFailCond
genNonFailCond vts cond =
  let condvars = nub (allVars cond)
  -- restrict variables to occurrences in cond:
  in (filter ((`elem` condvars) . fst) vts, cond)

--- Combine two non-fail conditions.
combineNonFailConds :: NonFailCond -> NonFailCond -> NonFailCond
combineNonFailConds (vts1,cond1) (vts2,cond2) =
  (union vts1 vts2, fcAnd cond1 cond2)

------------------------------------------------------------------------------
-- Replace all variables in a FlatCurry expression by their bindings
-- passed as a mapping from variables to expressions.
expandExpr :: [(Int,TypeExpr,Expr)] -> Expr -> Expr
expandExpr bs = expE
 where
  expE exp = case exp of
    Var v         -> maybe (Var v)
                           (\(_,_,e) -> if e == Var v then e else expE e)
                           (find (\(v',_,_) -> v' == v) bs)
    Lit _         -> exp
    Comb ct qf es -> Comb ct qf (map expE es)
    Or e1 e2      -> Or (expE e1) (expE e2)
    Free vs e     -> Free vs (expE e)
    Let vbs e     -> Let (map (\(v,ve) -> (v, expE ve)) vbs) (expE e)
    Case ct e brs -> Case ct (expE e)
                          (map (\(Branch p pe) -> Branch p (expE pe)) brs)
    Typed e t     -> Typed (expE e) t

------------------------------------------------------------------------------

--- The suffix of functions specifying non-fail conditions.
nonfailSuffix :: String
nonfailSuffix = "'nonfail"

--- Extracts explicit non-fail conditions specified in a module as
--- operations with suffix `'nonfail`.
nonFailCondsOfModule :: Prog -> [(QName,NonFailCond)]
nonFailCondsOfModule prog = map toNFCond nfconds
 where
  toNFCond fdecl = (stripNF (funcName fdecl),
                    (ruleTVars,
                     trRule (\_ exp -> exp) (const fcTrue) (funcRule fdecl)))
   where
    ruleTVars = zip (trRule (\args _ -> args) (const []) (funcRule fdecl))
                    (argTypes (funcType fdecl))

  stripNF (mn,fn) = (mn, take (length fn - length nonfailSuffix) fn)

  nfconds = filter ((nonfailSuffix `isSuffixOf`) . snd . funcName)
                   (progFuncs prog)

{-
preludeNonFailConds :: [(QName,[Expr])]
preludeNonFailConds = map (\divop -> (pre divop, [arg2NonZero])) divops
 where
  arg2NonZero = Comb FuncCall ("Prelude","/=") [Var 2, Lit (Intc 0)]
  divops = [ "_impl#div#Prelude.Integral#Prelude.Int"
           , "_impl#mod#Prelude.Integral#Prelude.Int"
           , "_impl#quot#Prelude.Integral#Prelude.Int"
           , "_impl#rem#Prelude.Integral#Prelude.Int"
           , "div", "mod", "quot", "rem" ]
-}

------------------------------------------------------------------------------
--- Prints a list of conditions for operations (if not empty).
--- The first argument contains all function declarations of the current module.
showConditions :: [FuncDecl] -> [(QName, NonFailCond)] -> String
showConditions fdecls = unlines . map showCond
 where
  showCond (qf,(_,cnd)) =
    let fdecl = maybe (error $
                       "showCondition: function '" ++ snd qf ++ "'' not found!")
                      id
                      (find (\fd -> funcName fd == qf) fdecls)
    in "\n-- Non-fail condition of operation `" ++ snd qf ++ "`:\n" ++
       showFuncDecl (genNonFailFunction fdecl cnd)

--- Generates the function representing the non-fail condition for a given
--- function and non-fail condition.
genNonFailFunction :: FuncDecl -> Expr -> FuncDecl
genNonFailFunction (Func (mn,fn) ar vis texp _) cnd =
  Func (mn, encodeContractName $ fn ++ nonfailSuffix) ar vis
       (nftype [1..ar] texp)
       (Rule [1..ar] (if all (`elem` [1..ar]) nfcondvars
                        then nfcondexp
                        else Free (nfcondvars \\ [1..ar]) nfcondexp))
 where
  nfcondexp = updCombs transClassImplOp (updCombs transTester (simpExpr cnd))
  nfcondvars = nub (allFreeVars nfcondexp)

  -- transform possible implementation of a class operation, e.g.,
  -- `_impl#minBound#Prelude.Bounded#Prelude.Char` -> `minBound :: Char`
  transClassImplOp ct qf@(mnf,fnf) args = case splitOn "#" fnf of
    [impl,fname,_,types] | impl == "_impl"
       -> maybe (Comb ct (mnf,fname) args)
                (Typed (Comb ct (mnf,fname) args))
                (typeString2TExp types)
    _  -> Comb ct qf args
   where
    typeString2TExp s | s == "Prelude.Bool"      = Just fcBool
                      | s == "Prelude.Char"      = Just fcChar
                      | s == "Prelude.Int"       = Just fcInt
                      | s == "Prelude.Float"     = Just fcFloat
                      | s == "Prelude.Ordering"  = Just fcOrdering
                      | otherwise                = Nothing

  nftype []     _     = TCons (pre "Bool") []
  nftype (v:vs) ftype = case ftype of
    FuncType t1 t2 -> FuncType t1 (nftype vs t2)
    ForallType _ t -> nftype (v:vs) t
    _              -> error "Illegal function type in genNonFailFunction"

-- Try to transform a possible test predicate for data constructors
-- generated by `Main.aCallType2Bool` (TODO: extend)
transTester :: CombType -> QName -> [Expr] -> Expr
transTester ct qf@(mnt,fnt) args
  | mnt == "Prelude" && "is-" `isPrefixOf` fnt
  = if fnt == "is-nil"
      then Comb ct (pre "null") args
      else if fnt == "is-insert"
              then fcNot (Comb ct (pre "null") args)
              else Comb ct qf args
  | otherwise = Comb ct qf args

--- Gets all free variables (i.e., without let/free/pattern bound variables)
--- occurring in an expression.
allFreeVars :: Expr -> [Int]
allFreeVars e = trExpr (:) (const id) comb lt fr (.) cas branch const e []
 where
  comb _ _ = foldr (.) id
  lt bs exp = (filter (`notElem` (map fst bs))) . exp . foldr (.) id (map snd bs)
  fr vs exp = (filter (`notElem` vs)) . exp
  cas _ exp bs = exp . foldr (.) id bs
  branch pat exp = (filter (`notElem` (args pat))) . exp
  args pat | isConsPattern pat = patArgs pat
           | otherwise = []

------------------------------------------------------------------------------
