-----------------------------------------------------------------------------
--- Definition and some operations for non-fail conditions.
---
--- @author  Michael Hanus
--- @version November 2025
---------------------------------------------------------------------------

module Verify.NonFailConditions
 where

import Data.List         ( (\\), find, isPrefixOf, isSuffixOf, nub
                         , splitOn, union )

import Contract.Names    ( encodeContractName )
import FlatCurry.Goodies
import FlatCurry.Names   ( anonCons )
import FlatCurry.Types

import FlatCurry.Build
import FlatCurry.Print
import FlatCurry.Simplify
import Verify.Helpers    ( unknownType )
import Verify.ProgInfo

--- Non-fail conditions are represented as a pair of typed variables
--- occurring in the conditions and a Boolean expression
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
expandExpr bs = updVars updvar
 where
  updvar v = maybe (Var v)
                   (\(_,_,e) -> if e == Var v then e else expandExpr bs e)
                   (find (\(v',_,_) -> v' == v) bs)

-- Replace all variables (even bound variables) in a FlatCurry expression
-- by new variables. Thus, the result is a renamed variant of the input.
renameAllVars :: [(Int,Int)] -> Expr -> Expr
renameAllVars rnm = rnmE
 where
  rnmE exp = case exp of
    Var v         -> Var (rnmV v)
    Lit _         -> exp
    Comb ct qf es -> Comb ct qf (map rnmE es)
    Or e1 e2      -> Or (rnmE e1) (rnmE e2)
    Free vs e     -> Free (map (\(v,vt) -> (rnmV v, vt)) vs) (rnmE e)
    Let vbs e     -> Let (map (\(v,vt,ve) -> (rnmV v,vt,rnmE ve)) vbs) (rnmE e)
    Case ct e brs -> Case ct (rnmE e)
                          (map (\(Branch p pe) -> Branch (rnmP p) (rnmE pe)) brs)
    Typed e t     -> Typed (rnmE e) t

  rnmV v = maybe v id (lookup v rnm)

  rnmP pat@(LPattern _) = pat
  rnmP (Pattern qc vs)  = Pattern qc (map rnmV vs)

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

------------------------------------------------------------------------------
--- Returns the non-fail condition for particular predefined operations
--- with non-trivial non-fail conditions.
lookupPredefinedNonFailCond :: QName -> Maybe NonFailCond
lookupPredefinedNonFailCond qf = lookup qf predefinedNonFailConds

predefinedNonFailConds :: [(QName,NonFailCond)]
predefinedNonFailConds =
  map (\divop -> (divop, (divargs fcInt, divcond int0))) intDivOps ++
  map (\divop -> (divop, (divargs fcFloat, divcond float0))) floatDivOps ++
  map (\sqop -> (pre sqop, sqrtcond)) sqrtops
 where
  divargs te = map (\i -> (i,te)) [1,2]
  divcond lit0 = fcNot (Comb FuncCall (pre "==") [Var 2, Lit lit0])
  int0 = Intc 0
  float0 = Floatc 0

  sqrtcond = ([(1,fcFloat)], Comb FuncCall (pre ">=") [Var 1, Lit float0])
  sqrtops = [ "_impl#sqrt#Prelude.Floating#Prelude.Float#", "sqrt" ]

--- Integer division operators defined in the prelude.
intDivOps :: [QName]
intDivOps = map pre
  [ "_impl#div#Prelude.Integral#Prelude.Int#"
  , "_impl#mod#Prelude.Integral#Prelude.Int#"
  , "_impl#quot#Prelude.Integral#Prelude.Int#"
  , "_impl#rem#Prelude.Integral#Prelude.Int#"
  , "div", "mod", "quot", "rem" ]

--- Float division operators defined in the prelude.
floatDivOps :: [QName]
floatDivOps = map pre
  [ "_impl#/#Prelude.Fractional#Prelude.Float#", "/" ]

------------------------------------------------------------------------------
--- Prints a list of conditions for operations (if not empty).
--- The first argument contains all function declarations of the current module.
showConditions :: [FuncDecl] -> [(QName, NonFailCond)] -> String
showConditions fdecls = unlines . map (showCondFunc . genNonFailFunction fdecls)
 where
  showCondFunc (fn,cf) =
    "\n-- Non-fail condition of operation `" ++ fn ++ "`:\n" ++
    showFuncDecl cf

--- Generates the function representing the non-fail condition for a given
--- function and non-fail condition.
--- The first argument is the list of all functions of the module.
genNonFailFunction :: [FuncDecl] -> (QName, NonFailCond) -> (String,FuncDecl)
genNonFailFunction fdecls (qfc,(_,cnd)) =
  maybe (error $ "genNonFailFunction: function '" ++ snd qfc ++ "'' not found!")
        (\fdecl -> genNonFailFunc fdecl)
        (find (\fd -> funcName fd == qfc) fdecls)
 where
  genNonFailFunc (Func (mn,fn) ar vis texp _) =
    (fn,
     Func (mn, encodeContractName $ fn ++ nonfailSuffix) ar vis
          (nftype [1..ar] texp)
          (Rule [1..ar] (if all (`elem` [1..ar]) nfcondvars
                           then nfcondexp
                           else Free (map (\v -> (v,unknownType))
                                          (nfcondvars \\ [1..ar]))
                                     nfcondexp)))
   where
    nftype []     _     = TCons (pre "Bool") []
    nftype (v:vs) ftype = case ftype of
      FuncType t1 t2 -> FuncType t1 (nftype vs t2)
      ForallType _ t -> nftype (v:vs) t
      _              -> error "Illegal function type in genNonFailFunction"

  nfcondexp = updCombs transClassImplOp (simpExpr cnd)
  nfcondvars = nub (allUnboundVars nfcondexp)

  -- transform possible implementation of a class operation, e.g.,
  -- `_impl#minBound#Prelude.Bounded#Prelude.Char#` -> `minBound :: Char`
  transClassImplOp ct qf@(mnf,fnf) args = case splitOn "#" fnf of
    [impl,fname,_,types,_] | impl == "_impl"
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

-- Generate a test predicate for a given data constructor and an expression.
-- generated by `Main.aCallType2Bool`.
transTester :: [(QName,ConsInfo)] -> QName -> Expr -> Expr
transTester consinfos qc exp
  | qc == pre "True"  = exp
  | qc == pre "False" = fcNot exp
  | qc == pre "[]"    = Comb FuncCall (pre "null") [exp]
  | qc == pre ":"     = fcNot (Comb FuncCall (pre "null") [exp])
  | otherwise
  = Case Rigid exp
      ([Branch (Pattern qc (take arity [100..])) fcTrue] ++
       if null siblings then [] else [Branch (Pattern anonCons []) fcFalse])
 where
  (arity,_,siblings) = infoOfCons consinfos qc

--- Gets all unbound variables (i.e., without let/free/pattern bound variables)
--- occurring in an expression.
allUnboundVars :: Expr -> [Int]
allUnboundVars e = trExpr (:) (const id) comb lt fr (.) cas branch const e []
 where
  comb _ _ = foldr (.) id
  lt bs exp = (filter (`notElem` (map (\(v,_,_) -> v) bs)))
              . exp . foldr (.) id (map (\(_,_,z) -> z) bs)
  fr vs exp = (filter (`notElem` map fst vs)) . exp
  cas _ exp bs = exp . foldr (.) id bs
  branch pat exp = (filter (`notElem` (args pat))) . exp
  args pat | isConsPattern pat = patArgs pat
           | otherwise = []

------------------------------------------------------------------------------
