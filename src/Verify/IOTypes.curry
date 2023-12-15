------------------------------------------------------------------------------
--- The definition of input/output types and operations to infer
--- and manipulate such types.
---
--- @author Michael Hanus
--- @version December 2023
------------------------------------------------------------------------------

module Verify.IOTypes
  ( InOutType(..), trivialInOutType, isAnyIOType, showIOT, inOutATypeFunc
  , VarTypes, VarTypesMap, ioVarType, showVarTypes, showArgumentVars
  , addVarType2Map, concVarTypesMap, setVarTypeInMap
  , bindVarInIOTypes, simplifyVarTypes
  )
 where

import Data.List
import Data.Maybe          ( mapMaybe )

import Analysis.TermDomain ( TermDomain(..), litAsCons )
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
--- It is parameterized over the abstract term domain.
data InOutType a = IOT [([a],a)]
  deriving Eq

--- The trivial `InOutType` for a function of a given arity.
trivialInOutType :: TermDomain a => Int -> InOutType a
trivialInOutType ar = IOT [(take ar (repeat anyType), anyType)]

-- Is the InOutType a general one, i.e., a mapping from Any's to Any?
isAnyIOType :: TermDomain a => InOutType a -> Bool
isAnyIOType (IOT iots) = case iots of
  [(ioargs,iores)] -> all (== anyType) (iores : ioargs)
  _                -> False

showIOT :: TermDomain a => InOutType a -> String
showIOT (IOT iots) = "{" ++ intercalate " || " (map showIOType iots) ++ "}"
 where
  showIOType (ict,oct) = "(" ++ intercalate "," (map showType ict) ++ ")" ++
                         " |-> " ++ showType oct

--- Get all possible result values from an InOutType.
valuesOfIOT :: TermDomain a => InOutType a -> a
valuesOfIOT (IOT iotypes) = foldr lubType emptyType (map snd iotypes)

--- Normalize InOutTypes by
--- * removing alternatives with empty output type
--- * joining results of IOTypes with identical arguments
normalizeIOT :: TermDomain a => InOutType a -> InOutType a
normalizeIOT (IOT iotypes) =
  IOT (joinOuts (filter ((/= emptyType) . snd) iotypes))
 where
  joinOuts []               = []
  joinOuts ((ict,oct):iots) =
    let (iots1,iots2) = partition ((== ict) . fst) iots
    in (ict, foldr1 lubType (oct : map snd iots1)) : joinOuts iots2

------------------------------------------------------------------------------
--- The state passed to compute call types contains a mapping from
--- variables (indices) to their positions and the current call pattern
--- for the operation to be analyzed.
data InOutTypeState a = InOutTypeState
  { currentOp :: QName                  -- the name of the current function
  , varPosPat :: [(Int,(Pos,CPattern))] -- variables and positions/patterns
  , ccPattern :: [CPattern]             -- current call pattern of the operation
  , resValue  :: (QName -> a)           -- analysis info about result values
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
pattern2AType :: TermDomain a => CPattern -> a
pattern2AType AnyP          = anyType
pattern2AType (ConsP qc ps) = aCons qc (map pattern2AType ps)


-- Add new variables not occurring in the left-hand side:
addNewVars :: TermDomain a => [Int] -> InOutTypeState a -> InOutTypeState a
addNewVars vs iost =
  iost { varPosPat = zip vs (map (\_ -> (freshVarPos,AnyP)) vs) ++
                     varPosPat iost }

-- Add new variable arguments under a given position.
addVarArgsAt :: TermDomain a => Pos -> [Int] -> InOutTypeState a
             -> InOutTypeState a
addVarArgsAt pos vs iost =
  iost { varPosPat = zip vs (map (\p -> (pos ++ [p],AnyP)) [0..]) ++
                     varPosPat iost }

-- Sets the pattern type of a variable (which already exists!).
setVarPattern :: TermDomain a => Int -> CPattern -> InOutTypeState a
              -> InOutTypeState a
setVarPattern vi vt iost =
  iost { varPosPat = 
           map (\ (v,(p,t)) -> if v==vi then (v,(p,vt)) else (v,(p,t)))
               (varPosPat iost) }

--- The initial state assumes that all arguments have type `Any`.
initInOutTypeState :: TermDomain a => QName -> [Int] -> (QName -> a)
                   -> InOutTypeState a
initInOutTypeState qf vs resval =
  InOutTypeState qf
                 (zip vs (map (\i -> ([i],AnyP)) [0..]))
                 (take (length vs) (repeat AnyP))
                 resval

--- Compute the in/out type for a function declaration w.r.t. a given
--- assignment of function names to result types.
inOutATypeFunc :: TermDomain a => (QName -> a) -> FuncDecl
               -> (QName,InOutType a)
inOutATypeFunc resval (Func qf ar _ _ rule) = case rule of
  Rule vs exp -> if length vs /= ar
                   then error $ "Func " ++ show qf ++ ": inconsistent arities"
                   else (qf,
                         normalizeIOT $
                           inOutATypeExpr (initInOutTypeState qf vs resval) exp)
  External _ -> (qf, IOT [(take ar (repeat anyType), resval qf)])

inOutATypeExpr :: TermDomain a => InOutTypeState a -> Expr -> InOutType a
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
---
--- In order to combine all in/out variables types for a variable,
--- we represent it by the variable and a disjunction of in/out types and
--- their argument variables, represented as a list. This disjunction
--- is defined by the following type:
type VarTypes a = [(InOutType a, [Int])]

--- The `VarTypesMap` is a mapping from variables to their variable types.
type VarTypesMap a = [(Int, VarTypes a)]


--- An abstract type represented as an input/output type for a variable.
ioVarType :: TermDomain a => a -> VarTypes a
ioVarType atype = [(IOT [([], atype)], [])]

--- Shows a list of input/output variables types.
showVarTypes :: TermDomain a => VarTypesMap a  -> String
showVarTypes = unlines . map showVarType
 where
  showVarType (rv, vts) =
    let vstr = 'v' : show rv ++ ": "
    in vstr ++
       intercalate ('\n' : take (length vstr) (repeat ' '))
         (map (\(iot,argvs) -> showIOT iot ++ " " ++ showArgumentVars argvs)
              vts)

--- Shows a list of argument variables in parentheses.
showArgumentVars :: [Int] -> String
showArgumentVars argvs =
  "(" ++ intercalate "," (map (\v -> 'v' : show v) argvs) ++ ")"

--- Adds variable types for a given variable to a `VarTypesMap`.
addVarType2Map :: TermDomain a
               => Int -> VarTypes a -> VarTypesMap a -> VarTypesMap a
addVarType2Map v vts = insert
 where
  insert []                             = [(v,vts)]
  insert ((v1,vts1) : vmap) | v == v1   = (v, vts1 ++ vts) : vmap
                            | v1 < v    = (v1,vts1) : insert vmap
                            | otherwise = (v,vts) : (v1,vts1) : vmap

--- Concatenates two `VarTypesMap`s.
concVarTypesMap :: TermDomain a
                => VarTypesMap a -> VarTypesMap a -> VarTypesMap a
concVarTypesMap vm1 vm2 = foldr (uncurry addVarType2Map) vm2 vm1

--- Replaces the variable types of a variable in a `VarTypesMap`.
setVarTypeInMap :: TermDomain a
                => Int -> VarTypes a -> VarTypesMap a -> VarTypesMap a
setVarTypeInMap v vts = replace
 where
  replace []                            = [(v,vts)]
  replace ((v1,vts1) : vmap) | v == v1   = (v, vts)  : vmap
                             | v1 < v    = (v1,vts1) : replace vmap
                             | otherwise = (v,vts)   : (v1,vts1) : vmap

--- Adds the binding of a variable to an abstract type (usually, the
--- abstract representation of a constructor) to the variable type map.
bindVarInIOTypes :: TermDomain a => Int -> a -> VarTypesMap a -> VarTypesMap a
bindVarInIOTypes var vatype vtsmap =
  setVarTypeInMap var (maybe [] (map bindIOResult) (lookup var vtsmap)) vtsmap
 where
  bindIOResult (IOT iots, vs) =
    ( IOT (filter ((/= emptyType) . snd) -- remove empty alternative types
                  (map (\ (ats,rt) -> (ats, joinType rt vatype)) iots))
    , vs)

--- Simplify a set of input/output variable types by exploiting
--- information about definitive abstract types (i.e., constructors).
simplifyVarTypes :: TermDomain a => VarTypesMap a -> VarTypesMap a
simplifyVarTypes = simpDefVarTypes []
 where
  simpDefVarTypes defts vartypes =
    let defvartypes = concatMap definitiveVarTypesFrom vartypes \\ defts
    in if null defvartypes -- no more definitive types available?
         then simpEmptyVarTypes [] vartypes
         else simpDefVarTypes (defts ++ defvartypes)
                              (propagateDefTypes defvartypes vartypes)

  -- Extracts the definitive type (arguments/results) from a given var type.
  -- A var type is definitive if it has one disjucnt and the in/out type
  -- in this disjunct has also exactly one disjunct.
  -- In this case, the result and argument variables have a definitive type
  -- if it is different from `anyType`.
  definitiveVarTypesFrom :: TermDomain a => (Int, VarTypes a) -> [(Int,a)]
  definitiveVarTypesFrom iot = case iot of
    (v, [(IOT [(ats,rt)], vs)]) -> filter (not . isAnyType . snd)
                                          ((v,rt) : zip vs ats)
    _                           -> []

  simpEmptyVarTypes evs vartypes =
    if null emptyvars then vartypes
                      else simpEmptyVarTypes (emptyvars ++ evs)
                                             (map propagateEmptyVars vartypes)
   where
    -- variables with an empty domain:
    emptyvars = concatMap getEmptyVar vartypes \\ evs
     where
      getEmptyVar (v, vts) = if IOT [] `elem` map fst vts then [v] else []

    propagateEmptyVars (v, vts) =
      (v, map (\ (IOT iots, vs) ->
                  if any (`elem` emptyvars) vs then (IOT []  , vs)
                                               else (IOT iots, vs)) vts)

  -- Propagate definite variable types into a set of in/out variable types:
  propagateDefTypes :: TermDomain a
                    => [(Int,a)] -> VarTypesMap a -> VarTypesMap a
  propagateDefTypes []           viots = viots
  propagateDefTypes ((v,vt):vts) viots =
    propagateDefTypes vts (map (propagateDefType (v,vt)) viots)

  -- Propagate a definite variable type into an in/out variable type
  -- by either refining the result types or argument types:
  propagateDefType (v,vt) (v1, vts)  -- [(IOT iots, vs1)]
    | v == v1 -- propagate the definite result into the input/output type:
    = ( v1
      , map (\ (IOT iots, vs1) -> 
                (IOT (filter ((/= emptyType) . snd)
                     (map (\ (at,rt) -> (at, joinType rt vt)) iots)), vs1))
            vts )
    | otherwise
    = ( v1
      , map (\ (IOT iots, vs1) ->
             if  v `elem` vs1 -- propagate a def. argument into in/out type:
               then -- delete incompatible argument types:
                    (maybe (IOT iots) -- should not occur
                           (\i -> IOT (filter (all (not . isEmptyType) . fst)
                                        (map (\ (at,rt) ->
                                                (replace (joinType (at!!i) vt)
                                                         i at, rt))
                                             iots)))
                           (elemIndex v vs1), vs1)
               else (IOT iots, vs1))
            vts )

------------------------------------------------------------------------------
