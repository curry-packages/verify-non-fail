------------------------------------------------------------------------------
--- The definition of input/output types and operations to infer
--- and manipulate such types.
---
--- @author Michael Hanus
--- @version September 2023
------------------------------------------------------------------------------

module Verify.IOTypes
  ( InOutType(..), isAnyIOType, showIOT, inOutATypeFunc
  , VarType, showVarTypes, showArgumentVars, simplifyVarTypes, bindVarInIOTypes
  )
 where

import Data.List
import Data.Maybe      ( mapMaybe )
import Analysis.Values ( AType, emptyType, anyType, aCons, lit2cons
                       , joinAType, lubAType, showAType )
import FlatCurry.Types

import Debug.Trace ( trace )

import Verify.Helpers

------------------------------------------------------------------------------
-- The implementation of an anlysis to get the input/output types of operations.
-- The input/output type is a disjunction of input/output type pairs.
-- This is useful to infer call-types as well as output types of operations.
-- Nevertheless, the output types should be inferred by a standard
-- fixpoint analysis and the analysis results can be used here.

--- An InOutType is a disjunction, represented as a list,
--- of input/output type pairs.
data InOutType = IOT [([AType],AType)]
  deriving Eq

-- Is the InOutType a general one, i.e., a mapping from Any's to Any?
isAnyIOType :: InOutType -> Bool
isAnyIOType (IOT iots) = case iots of
  [(ioargs,iores)] -> all (== anyType) (iores : ioargs)
  _                -> False

showIOT :: InOutType -> String
showIOT (IOT iots) = "{" ++ intercalate " || " (map showIOType iots) ++ "}"
 where
  showIOType (ict,oct) = "(" ++ intercalate "," (map showAType ict) ++ ")" ++
                         " |-> " ++ showAType oct

--- Normalize InOutTypes by joining results of IOTypes with identical arguments.
normalizeIOT :: InOutType -> InOutType
normalizeIOT (IOT iotypes) = IOT (norm iotypes)
 where
  norm []               = []
  norm ((ict,oct):iots) =
    let (iots1,iots2) = partition ((== ict) . fst) iots
    in (ict, foldr1 lubAType (oct : map snd iots1)) : norm iots2

------------------------------------------------------------------------------
--- The state passed to compute call types contains a mapping from
--- variables (indices) to their positions and the current call type
--- for the operation to be analyzed.
data InOutTypeState = InOutTypeState
  { currentOp   :: QName               -- the name of the current function
  , varPosAType :: [(Int,(Pos,AType))] -- variable and their positions/types
  , ccAType     :: [AType]             -- current call type of the operation
  , resValue    :: (QName -> AType)    -- analysis info about result values
  }

-- Add new variables not occurring in the left-hand side:
addNewAVars :: [Int] -> InOutTypeState -> InOutTypeState
addNewAVars vs iost =
  iost { varPosAType = zip vs (map (\_ -> (freshVarPos,anyType)) vs) ++
                       varPosAType iost }

-- Sets the type of a variable (which already exists!).
setVarType :: Int -> AType -> InOutTypeState -> InOutTypeState
setVarType vi vt iost =
  iost { varPosAType = 
           map (\ (v,(p,t)) -> if v==vi then (v,(p,vt)) else (v,(p,t)))
               (varPosAType iost) }

--- The initial state assumes that all arguments have type `Any`.
initInOutTypeState :: QName -> [Int] -> (QName -> AType) -> InOutTypeState
initInOutTypeState qf vs resval =
  InOutTypeState qf (zip vs (map (\i -> ([i],anyType)) [0..]))
                 (take (length vs) (repeat anyType))
                 resval

inOutATypeFunc :: (QName -> AType) -> FuncDecl -> (QName,InOutType)
inOutATypeFunc resval (Func qf ar _ _ rule) = case rule of
  Rule vs exp -> if length vs /= ar
                   then error $ "Func " ++ show qf ++ ": inconsistent arities"
                   else (qf,
                         normalizeIOT $
                           inOutATypeExpr (initInOutTypeState qf vs resval) exp)
  External _ -> (qf, IOT [(take ar (repeat anyType), resval qf)])

inOutATypeExpr :: InOutTypeState -> Expr -> InOutType
inOutATypeExpr tst exp = case exp of
  Var v         -> maybe (varNotFound v)
                         (\ (_,ct) -> IOT [(ccAType tst, ct)])
                         (lookup v (varPosAType tst))
  Lit l         -> IOT [(ccAType tst, aCons (lit2cons l))]
  Comb ct qf _  -> if ct == FuncCall
                     then IOT [(ccAType tst, resValue tst qf)]
                     else IOT [(ccAType tst, aCons qf)]
  Let vs e      -> inOutATypeExpr (addNewAVars (map fst vs) tst) e
                    -- TODO: make let analysis more precise
  Free vs e     -> inOutATypeExpr (addNewAVars vs tst) e
  Or e1 e2      -> combineIOTs (inOutATypeExpr tst e1)
                               (inOutATypeExpr tst e2)
  Case _ ce bs  -> case ce of
                     Var v -> foldr1 combineIOTs
                               (map (\ (Branch p e) ->
                                     inOutATypeExpr (addVarBranchPattern v p) e)
                                    bs)
                     _     -> foldr1 combineIOTs
                               (map (\ (Branch p e) ->
                                     inOutATypeExpr (addBranchPattern p) e)
                                    bs)
  Typed e _     -> inOutATypeExpr tst e
 where
  varNotFound v = error $ "Function " ++ snd (currentOp tst) ++
                          ": variable " ++ show v ++ " not found"

  combineIOTs (IOT iots1) (IOT iots2) = IOT (iots1 ++ iots2)

  addVarBranchPattern v pat
    | isFreshVarPos vpos
    = addNewAVars (patternArgs pat) tst -- fresh var, do not change call type
    | otherwise
    = case pat of Pattern _ vs -> addNewAVars vs tst'
                  LPattern _   -> tst'
   where
    consOfPat = case pat of Pattern qc _ -> qc
                            LPattern l   -> lit2cons l
    tst' = (setVarType v (aCons consOfPat) tst)
             { ccAType = setACons2CT consOfPat vpos (ccAType tst) }
    vpos = maybe (varNotFound v) fst (lookup v (varPosAType tst))

  addBranchPattern (Pattern _ vs) = addNewAVars vs tst
  addBranchPattern (LPattern _)   = tst

  -- Sets a constructor for a position in a given list of argument types.
  setACons2CT :: QName -> Pos -> [AType] -> [AType]
  setACons2CT _  []  ats = trace "setACons2CT: root occurrence" ats
  setACons2CT qc [p] ats = replace (joinAType (aCons qc) (ats!!p)) p ats
  setACons2CT _  ps@(_:_:_) ats =
    trace ("setACons2CT: deep position occurred: " ++ show ps) ats


------------------------------------------------------------------------------
-- Handling input/output variable types.

--- An input/output variable type `(v,iot,vs)` consists of
--- * a variable `v`
--- * an input/output type `iot` specifying the result of `v`, i.e.,
---   either the input/output type of the function bound to `v` or
---   simply `{() |-> any}` if the variable is unbound
--- * the list `vs` of arguments of the function to which `v` is bound
---   (which could be empty).
type VarType = (Int,InOutType,[Int])

--- Shows a list of input/output variables types.
showVarTypes :: [VarType] -> String
showVarTypes = unlines . map showVarType
 where
  showVarType (rv, iot, argvs) =
    'v' : show rv ++ ": " ++ showIOT iot ++ " " ++ showArgumentVars argvs

--- Shows a list of argument variables in parentheses.
showArgumentVars :: [Int] -> String
showArgumentVars argvs =
  "(" ++ intercalate "," (map (\v -> 'v' : show v) argvs) ++ ")"

--- Simplify a set of input/output variable types.
simplifyVarTypes :: [VarType] -> [VarType]
simplifyVarTypes = simpDefVarTypes []
 where
  simpDefVarTypes defts vartypes =
    let defvartypes = (concatMap definitiveVarTypesFrom vartypes) \\ defts
    in if null defvartypes -- no more definitive types available?
         then simpEmptyVarTypes [] vartypes
         else simpDefVarTypes (defts ++ defvartypes)
                              (propagateDefTypes defvartypes vartypes)

  simpEmptyVarTypes evs vartypes =
    if null emptyvars
      then vartypes
      else simpEmptyVarTypes (emptyvars ++ evs)
                             (map propagateEmptyVars vartypes)
   where
    -- variables with an empty domain:
    emptyvars = mapMaybe getEmptyVar vartypes \\ evs
     where getEmptyVar iot = case iot of (v, IOT [], _) -> Just v
                                         _              -> Nothing

    propagateEmptyVars (v, IOT iots, vs) =
      if any (`elem` emptyvars) vs then (v, IOT [], vs)
                                   else (v, IOT iots, vs)

  -- Extracts the definitive types (arguments/results) from a given var type.
  definitiveVarTypesFrom :: VarType -> [(Int,AType)]
  definitiveVarTypesFrom iot = case iot of
    (v, IOT [(ats,rt)], vs) -> filter ((/= anyType) . snd) ((v,rt) : zip vs ats)
    _                       -> []

  -- propagate definite variable types into a set of in/out variable types:
  propagateDefTypes :: [(Int,AType)] -> [VarType] -> [VarType]
  propagateDefTypes []           viots = viots
  propagateDefTypes ((v,vt):vts) viots =
    propagateDefTypes vts (map (propagateDefType (v,vt)) viots)

  -- propagate a definite variable type into an in/out variable type
  -- by either refining the result types or argument types:
  propagateDefType :: (Int,AType) -> VarType -> VarType
  propagateDefType (v,vt) (v1, IOT iots, vs1)
    | v == v1 -- propagate the definite result into the input/output type:
    = ( v1
      , IOT (filter ((/= emptyType) . snd)
                    (map (\ (at,rt) -> (at, joinAType rt vt)) iots))
      , vs1)
    | v `elem` vs1 -- propagate a definitive argument into the in/out type:
    = ( v1         -- delete incompatible argument types:
      , maybe (IOT iots) -- should not occur
              (\i -> IOT (filter (all (/= emptyType) . fst)
                            (map (\ (at,rt) ->
                                   (replace (joinAType (at!!i) vt) i at, rt))
                                 iots)))
              (elemIndex v vs1)
      , vs1)
    | otherwise
    = (v1, IOT iots, vs1)

--- Adds the binding of a variable to a constructor to the set of
--- input/output types for variables.
bindVarInIOTypes :: Int -> QName -> [VarType] -> [VarType]
bindVarInIOTypes var qc = map bindVar
 where
  bindVar (v, IOT iots, vs)
    | var /= v  = (v, IOT iots, vs)
    | otherwise
    = (v, IOT (filter ((/= emptyType) . snd) -- remove empty alternative types
                 (map (\ (ats,rt) -> (ats, joinAType rt (aCons qc)))
                      iots)), vs)

------------------------------------------------------------------------------
