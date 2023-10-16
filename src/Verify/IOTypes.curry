------------------------------------------------------------------------------
--- The definition of input/output types and operations to infer
--- and manipulate such types.
---
--- @author Michael Hanus
--- @version September 2023
------------------------------------------------------------------------------

module Verify.IOTypes
  ( InOutType(..), trivialInOutType, isAnyIOType, showIOT, inOutATypeFunc
  , VarType, ioVarType, showVarTypes, showArgumentVars, simplifyVarTypes
  , bindVarInIOTypes
  )
 where

import Data.List
import Data.Maybe      ( mapMaybe )

import FlatCurry.Types

import Debug.Trace ( trace )

import Verify.Domain
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

--- The trivial `InOutType` for a function of a given arity.
trivialInOutType :: Int -> InOutType
trivialInOutType ar = IOT [(take ar (repeat anyType), anyType)]

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

--- Get all possible result values from an InOutType.
valuesOfIOT :: InOutType -> AType
valuesOfIOT (IOT iotypes) = foldr lubAType emptyType (map snd iotypes)

--- Normalize InOutTypes by
--- * removing alternatives with empty output type
--- * joining results of IOTypes with identical arguments
normalizeIOT :: InOutType -> InOutType
normalizeIOT (IOT iotypes) =
  IOT (joinOuts (filter ((/= emptyType) . snd) iotypes))
 where
  joinOuts []               = []
  joinOuts ((ict,oct):iots) =
    let (iots1,iots2) = partition ((== ict) . fst) iots
    in (ict, foldr1 lubAType (oct : map snd iots1)) : joinOuts iots2

------------------------------------------------------------------------------
--- The state passed to compute call types contains a mapping from
--- variables (indices) to their positions and the current call type
--- for the operation to be analyzed.
data InOutTypeState = InOutTypeState
  { currentOp :: QName                  -- the name of the current function
  , varPosPat :: [(Int,(Pos,CPattern))] -- variables and positions/patterns
  , ccPattern :: [CPattern]             -- current call pattern of the operation
  , resValue  :: (QName -> AType)       -- analysis info about result values
  }

-- Representation of constructor patterns:
data CPattern = AnyP | ConsP QName [CPattern]
 deriving (Eq,Show)

-- `replacePattern pat pos spat` puts `spat` in `pat` at position `pos`.
replacePattern :: CPattern -> Pos -> CPattern -> CPattern
replacePattern _               []     spat = spat
replacePattern AnyP            (_:_)  _    = error "replacePattern: AnyP"
replacePattern (ConsP qn pats) (p:ps) spat =
  if p >= length pats
    then error "replacePattern: illegal position"
    else ConsP qn (replace (replacePattern (pats!!p) ps spat) p pats)

-- Transform a constructor pattern into an abstract type.
pattern2AType :: CPattern -> AType
pattern2AType AnyP          = anyType
pattern2AType (ConsP qc ps) = aCons qc (map pattern2AType ps)


-- Add new variables not occurring in the left-hand side:
addNewVars :: [Int] -> InOutTypeState -> InOutTypeState
addNewVars vs iost =
  iost { varPosPat = zip vs (map (\_ -> (freshVarPos,AnyP)) vs) ++
                     varPosPat iost }

-- Add new variable arguments under a given position.
addVarArgsAt :: Pos -> [Int] -> InOutTypeState -> InOutTypeState
addVarArgsAt pos vs iost =
  iost { varPosPat = zip vs (map (\p -> (pos ++ [p],AnyP)) [0..]) ++
                     varPosPat iost }

-- Sets the pattern type of a variable (which already exists!).
setVarPattern :: Int -> CPattern -> InOutTypeState -> InOutTypeState
setVarPattern vi vt iost =
  iost { varPosPat = 
           map (\ (v,(p,t)) -> if v==vi then (v,(p,vt)) else (v,(p,t)))
               (varPosPat iost) }

--- The initial state assumes that all arguments have type `Any`.
initInOutTypeState :: QName -> [Int] -> (QName -> AType) -> InOutTypeState
initInOutTypeState qf vs resval =
  InOutTypeState qf
                 (zip vs (map (\i -> ([i],AnyP)) [0..]))
                 (take (length vs) (repeat AnyP))
                 resval

--- Compute the in/out type for a function declaration w.r.t. a given
--- assignment of function names to result types.
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
                         (\ (_,ct) -> IOT [(cpatAsAType, pattern2AType ct)])
                         (lookup v (varPosPat tst))
  Lit l         -> IOT [(cpatAsAType, aLit l)]
  Comb ct qf es -> if ct == FuncCall
                     then IOT [(cpatAsAType, resValue tst qf)]
                     else let argtypes = map (valuesOfIOT . inOutATypeExpr tst)
                                             es
                          in IOT [(cpatAsAType, aCons qf argtypes)]
  Let vs e      -> inOutATypeExpr (addNewVars (map fst vs) tst) e
                    -- TODO: make let analysis more precise
  Free vs e     -> inOutATypeExpr (addNewVars vs tst) e
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
  cpatAsAType = map pattern2AType (ccPattern tst)

  varNotFound v = error $ "Function " ++ snd (currentOp tst) ++
                          ": variable " ++ show v ++ " not found"

  combineIOTs (IOT iots1) (IOT iots2) = IOT (iots1 ++ iots2)

  addVarBranchPattern v pat
    | isFreshVarPos vpos
    = addNewVars (patternArgs pat) tst -- fresh var, do not change call type
    | otherwise
    = --trace ("Variable " ++ show v ++ " at position " ++ show vpos) $
      case pat of Pattern _ vs -> addVarArgsAt vpos vs tst'
                  LPattern _   -> tst'
   where
    vpos = maybe (varNotFound v) fst (lookup v (varPosPat tst))

    consPattern = case pat of
                    Pattern qc vs -> ConsP qc (take (length vs) (repeat AnyP))
                    LPattern l    -> ConsP (litAsCons l) []

    tst' = (setVarPattern v consPattern tst)
              { ccPattern = setPatternAtPos consPattern vpos (ccPattern tst) }

  addBranchPattern (Pattern _ vs) = addNewVars vs tst
  addBranchPattern (LPattern _)   = tst

  -- Sets a pattern at a position in a given list of patterns.
  setPatternAtPos :: CPattern -> Pos -> [CPattern] -> [CPattern]
  setPatternAtPos _  []     pts = trace "setPatternAtPos: root occurrence" pts
  setPatternAtPos pt (p:ps) pts = replace (replacePattern (pts!!p) ps pt) p pts

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

--- A variable with a type represented as an input/output variable type.
ioVarType :: Int -> AType -> VarType
ioVarType v atype = (v, IOT [([], atype)], [])

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

  -- Propagate definite variable types into a set of in/out variable types:
  propagateDefTypes :: [(Int,AType)] -> [VarType] -> [VarType]
  propagateDefTypes []           viots = viots
  propagateDefTypes ((v,vt):vts) viots =
    propagateDefTypes vts (map (propagateDefType (v,vt)) viots)

  -- Propagate a definite variable type into an in/out variable type
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

--- Adds the binding of a variable to an abstract type (the representation
--- of a constructor) to the set of input/output types for variables.
bindVarInIOTypes :: Int -> AType -> [VarType] -> [VarType]
bindVarInIOTypes var vatype = map bindVar
 where
  bindVar (v, IOT iots, vs)
    | var /= v  = (v, IOT iots, vs)
    | otherwise
    = (v, IOT (filter ((/= emptyType) . snd) -- remove empty alternative types
                 (map (\ (ats,rt) -> (ats, joinAType rt vatype))
                      iots)), vs)

------------------------------------------------------------------------------
