module Verify.NonFailConditions
 where

import Data.List         ( nub, union )

import FlatCurry.Goodies
import FlatCurry.Types

import FlatCurry.Build

--- Non-fail conditions are represented as a pair of typed variables
--- occurring in the conditions and a list (conjunction) of Boolean
--- expressions (in FlatCurry representation).
type NonFailCond = ([(Int,TypeExpr)], [Expr])

--- The always unsatisfiable non-fail condition.
nfcFalse :: NonFailCond
nfcFalse = ([],[fcFalse])

--- Generate a non-fail condition from a list of variables types
--- and a list of Boolean expressions.
genNonFailCond :: [(Int,TypeExpr)] -> [Expr] -> NonFailCond
genNonFailCond vts cond =
  let condvars = nub (concatMap allVars cond)
  -- restrict variables to occurrences in cond:
  in (filter ((`elem` condvars) . fst) vts, cond)

--- Combine two non-fail conditions.
combineNonFailConds :: NonFailCond -> NonFailCond -> NonFailCond
combineNonFailConds (vts1,cond1) (vts2,cond2) =
  (union vts1 vts2, union cond1 cond2)
