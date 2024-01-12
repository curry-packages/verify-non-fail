------------------------------------------------------------------------------
--- The definition of call types and an operation to infer them.
---
--- @author Michael Hanus
--- @version January 2024
------------------------------------------------------------------------------

module Verify.CallTypes where

import Data.List

import Analysis.TermDomain ( TermDomain(..), litAsCons )
import FlatCurry.Files
import FlatCurry.Goodies
import FlatCurry.Types

import FlatCurry.Build     ( pre )
import Verify.Helpers
import Verify.Options

------------------------------------------------------------------------------
--- A call type is intended to specify the conditions on arguments
--- so that a function call satisfying the call type is reducible
--- (i.e., some rule matches).
---
--- A call type is either `AnyT` (any term matches) or a list of
--- possible constructors with their argument call types.
--- Note that literals `l` are represented as `MCons [(("",l),[])]`.
--- This also implies that their siblings are unknown.
data CallType = AnyT | MCons [(QName,[CallType])]
 deriving (Eq,Read,Show)

--- The call type of an operation which has no non-failing arguments.
failCallType :: [[CallType]]
failCallType = []

--- Is the call type a failure call type?
isFailCallType :: [[CallType]] -> Bool
isFailCallType = null

-- Shows a call type in a prettier way.
prettyCT :: CallType -> String
prettyCT AnyT       = "_"
prettyCT (MCons cs) = "{" ++ intercalate " | " (map prettyC cs) ++ "}"
 where
  prettyC (qc,args)      = snd qc ++ prettyArgs args
  prettyArgs []          = ""
  prettyArgs args@(_:_) = "(" ++ intercalate "," (map prettyCT args) ++ ")"

prettyFunCallTypes :: [[CallType]] -> String
prettyFunCallTypes cts =
  if isFailCallType cts
    then "<FAILING>"
    else intercalate " | " $ map prettyCallTypeArgs cts

prettyCallTypeArgs :: [CallType] -> String
prettyCallTypeArgs cts = case cts of
  []   -> "()"
  [ct] -> prettyCT ct
  _    -> "(" ++ intercalate ", " (map prettyCT cts) ++ ")"


--- Simplify call types by recursively transforming each complete
--- list of constructors with `AnyT` arguments to `AnyT`.
simpFuncCallType :: [[(QName,Int)]] -> [[CallType]] -> [[CallType]]
simpFuncCallType allcons ctss =
  let ctss' = foldr addCTArgs [] (map (map simpCallType) ctss)
  in if ctss' == ctss then ctss
                      else simpFuncCallType allcons ctss'
 where
  simpCallType AnyT = AnyT
  simpCallType (MCons qcts) =
    complete2Any (map (\ (qc,cts) -> (qc, map simpCallType cts)) qcts)
   where
    complete2Any [] = MCons []
    complete2Any cs@(_:_)
      | all (== AnyT) (concatMap snd cs) && -- all arguments AnyT?
        isCompleteConstructorList allcons (map fst cs)
      = AnyT
      | otherwise = MCons cs

-- Join two  call types.
joinCT :: CallType -> CallType -> CallType
joinCT AnyT          ct           = ct
joinCT (MCons tcs1) AnyT          = MCons tcs1
joinCT (MCons tcs1) (MCons tcs2) =
  MCons (intersect tcs1 tcs2) --TODO: refine

-- Least-upper bound (union) of call types.
unionCT :: CallType -> CallType -> CallType
unionCT AnyT       _          = AnyT
unionCT (MCons _)  AnyT       = AnyT
unionCT (MCons m1) (MCons m2) = MCons (foldr insertCT m1 m2)
 where

--- Least-upper bound (union) on lists of argument call types.
unionCTs :: [[CallType]] -> [[CallType]] -> [[CallType]]
unionCTs cts1 cts2 = foldr addCTArgs cts1 cts2

--- Adds a new list of argument types to a given list of alternative arg types
addCTArgs :: [CallType] -> [[CallType]] -> [[CallType]]
addCTArgs cts0 [] = [cts0]
addCTArgs cts0 (cts:mcts)
  | diffs == 0 = cts : mcts
  | diffs > 1  = cts0 : cts : mcts
  | otherwise  = combineOneDiffCT cts0 cts : mcts
 where
  diffs = numDiffs cts0 cts  -- number of different arguments

--- Combine to argument call types having exact one different argument.
combineOneDiffCT :: [CallType] -> [CallType] -> [CallType]
combineOneDiffCT []    []    = []
combineOneDiffCT []    (_:_) = error "combineOneDiffCT: inconsistent arguments"
combineOneDiffCT (_:_) []    = error "combineOneDiffCT: inconsistent arguments"
combineOneDiffCT (ct1:cts1) (ct2:cts2)
  | ct1 == ct2 = ct1 : combineOneDiffCT cts1 cts2
  | otherwise  = unionCT ct1 ct2 : cts1

-- Insert a call constructor with arguments into a given list of cons types.
insertCT :: (QName,[CallType]) -> [(QName,[CallType])] -> [(QName,[CallType])]
insertCT (qc,qcas) [] = [(qc,qcas)]
insertCT (qc,qcas) ((qc1,qc1as) : mcs)
  | qc == qc1
  = if diffs == 0 then (qc, qcas) : mcs
                  else if diffs > 1
                         then (qc,qcas) : (qc,qc1as) : mcs -- cannot combine
                         else (qc, combineOneDiffCT qcas qc1as) : mcs
  | otherwise = (qc1,qc1as) : insertCT (qc,qcas) mcs
 where
  diffs = numDiffs qcas qc1as -- number of different arguments


--- Count the number of pairwise different elements in a list.
numDiffs :: Eq a => [a] -> [a] -> Int
numDiffs xs ys = sum (map (\ (x,y) -> if x == y then 0 else 1) (zip xs ys))

-- Describes a list of alternative call types a totally reducible operation?
isTotalCallType :: [[CallType]] -> Bool
isTotalCallType cts = not (null cts) && all (all (==AnyT)) cts

------------------------------------------------------------------------------

--- Adds a constructor with a given arity at a position
--- to a given list of argument call types.
addCons2CT :: QName -> Int -> Pos -> [CallType] -> [CallType]
addCons2CT _  _  []     _   = error "addCons2CT: try to add constructor at root"
addCons2CT qc ar (p:ps) cts = replace (addConsInCT qc ar ps (cts!!p)) p cts

addConsInCT :: QName -> Int -> Pos -> CallType -> CallType
addConsInCT qc ar []     ct          =
  joinCT ct (MCons [(qc, take ar (repeat AnyT))])
addConsInCT qc ar (p:ps) (MCons tcs) =
  MCons (map (\ (c,ts) -> (c, addCons2CT qc ar (p:ps) ts)) tcs)
addConsInCT qc _  (p:ps) AnyT         =
  error $ "addCons2CT: deep position " ++ show (p:ps) ++
          " occurred for constructor " ++ snd qc ++ " in AnyT"

testAddCons2CT1 :: [CallType]
testAddCons2CT1 = addCons2CT (pre "[]") 0 [1] [AnyT,AnyT]
testAddCons2CT2 :: [CallType]
testAddCons2CT2 = addCons2CT (pre ":") 2 [0] [AnyT,AnyT]

------------------------------------------------------------------------------
-- The implementation of an anlysis to get the call types of an operation.
-- This is useful to infer nonfailing conditions w.r.t. standard types.

--- The state passed to compute call types contains a mapping from
--- variables (indices) to their positions and the call type of the
--- current branch of the operation to be analyzed.
data CallTypeState = CallTypeState
  { ctstCurrFunc :: QName       -- the name of the current function
  , ctstVarPos   :: [(Int,Pos)]
  , ctstCallType :: [CallType]
  , ctstToolOpts :: Options
  }


initCallTypeState :: Options -> QName -> [Int] -> CallTypeState
initCallTypeState opts qf vs =
  CallTypeState qf (zip vs (map (\i -> [i]) [0..]))
                (take (length vs) (repeat AnyT)) opts

--- Computes the call type of a function where all constructors are
--- provided as the second argument.
--- The computed call type for an `n`-ary function is a disjunction
--- (represented as a list) of alternative call types
--- where each element in the disjunction is list of `n` call types for
--- each argument.
callTypeFunc :: Options -> [[(QName,Int)]] -> FuncDecl -> (QName,[[CallType]])
callTypeFunc opts allcons (Func qf ar _ _ rule) =
  maybe
    (case rule of
       External _  -> callTypeExternalFunc qf ar
       Rule vs exp ->
         if length vs /= ar
           then error $ "Func " ++ show qf ++ ": inconsistent variables"
           else (qf, simpFuncCallType allcons
                       (callTypeExpr (initCallTypeState opts qf vs) exp)))
     (\ct -> (qf,ct))
     (lookup qf defaultCallTypes)

--- Some call types for predefined operations.
--- The fail call types for arithmetic operations could be improved
--- in the future by considering refined number types.
defaultCallTypes :: [(QName,[[CallType]])]
defaultCallTypes =
  map (\qf -> (pre qf, failCallType))
      [ "=:=", "=:<=", "=:<<="
      , "div", "divFloat", "prim_divFloat", "divInt", "prim_divInt"
      , "mod", "modInt", "prim_modInt"
      , "quot", "quotInt", "prim_quotInt"
      , "rem", "remInt", "prim_remInt"
      , "_impl#div#Prelude.Integral#Prelude.Int"
      , "_impl#mod#Prelude.Integral#Prelude.Int"
      , "_impl#quot#Prelude.Integral#Prelude.Int"
      , "_impl#rem#Prelude.Integral#Prelude.Int"
      , "sqrtFloat", "prim_sqrtFloat"
      ] ++
  [ (pre "&",   [[MCons [(pre "True",[])], MCons [(pre "True",[])]]])
  , (pre "cond",[[MCons [(pre "True",[])], AnyT]])
  , (pre "aValueChar",[[]])
  ]

--- Computes the call type of an external (primitive) function.
--- Currently, we assume that they are total functions.
callTypeExternalFunc :: QName -> Int -> (QName,[[CallType]])
callTypeExternalFunc qf ar
  | qf == pre "failed" = (qf, [])
  | otherwise          = (qf, [take ar (repeat AnyT)])

-- Add new variables not occurring in the left-hand side:
addFreshVars :: [Int] -> CallTypeState -> CallTypeState
addFreshVars vs ctst =
  ctst { ctstVarPos = ctstVarPos ctst ++ map (\vi -> (vi, freshVarPos)) vs }

callTypeExpr :: CallTypeState -> Expr -> [[CallType]]
callTypeExpr ctst exp = case exp of
  Var _         -> [ctstCallType ctst]
  Lit _         -> [ctstCallType ctst]
  Comb _ _ _    -> [ctstCallType ctst]
  Let bs e      -> callTypeExpr (addFreshVars (map fst bs) ctst) e
  Free vs e     -> callTypeExpr (addFreshVars vs ctst) e
  Or e1 e2      -> unionCTs (callTypeExpr ctst e1) (callTypeExpr ctst e2)
  Case _ ce bs  ->
    case ce of
      Var v -> foldr1 unionCTs
                      (map (\ (Branch p e) ->
                                 callTypeExpr (addVarBranchPattern v p) e)
                           (filter (not . isFailedBranch) bs))
      _     -> foldr1 unionCTs
                      (map (\ (Branch p e) ->
                                 callTypeExpr (addBranchPattern p) e)
                           (filter (not . isFailedBranch) bs))
  Typed e _     -> callTypeExpr ctst e
 where
  varNotFound v = error $ "Function " ++ snd (ctstCurrFunc ctst) ++
                          ": variable " ++ show v ++ " not found"

  isFailedBranch (Branch _ e) = case e of
    Comb FuncCall qf _ -> qf == pre "failed" ||
                          (optError (ctstToolOpts ctst) && qf == pre "error")
    _                  -> False

  addVarBranchPattern v pat
    | isFreshVarPos vpos
    = -- since the variable is fresh, we cannot specialize the call type
      addFreshVars (patternArgs pat) ctst
    | otherwise
    = case pat of
        Pattern qc vs -> ctst { ctstCallType = addCons2CT qc (length vs) vpos
                                                        (ctstCallType ctst)
                              , ctstVarPos = ctstVarPos ctst ++
                                             map (\ (vi,i) -> (vi, vpos ++ [i]))
                                                 (zip vs [0..]) }
        LPattern lit  -> ctst { ctstCallType = addCons2CT (litAsCons lit) 0 vpos
                                                          (ctstCallType ctst) }
   where vpos = maybe (varNotFound v) id (lookup v (ctstVarPos ctst))

  addBranchPattern (Pattern _ vs) = addFreshVars vs ctst
  addBranchPattern (LPattern _)   = ctst

------------------------------------------------------------------------------
-- An abstract call type of an operation (parameterized over the abstract
-- domain) is either `Nothing` in case of an always failing operation,
-- or just a list of abstract types for the arguments.
-- In the following we provide some operations on abstract call types.
type ACallType a = Maybe [a]

--- Transforms a call type for an operation, i.e., a disjunction of a list
--- of alternative call types for the arguments, into an abstract call type.
--- Since the abstract call type of an operation is a single list of abstract
--- call types for the arguments so that a disjunction of argument lists
--- cannot be expressed, the disjunctions are joined (i.e., intersected).
funcCallType2AType :: TermDomain a => [[(QName,Int)]] -> (QName, [[CallType]])
                   -> (QName, ACallType a)
funcCallType2AType allcons (qn,fct) =
  (qn, if null fct
         then failACallType
         else foldr1 joinACallType (map callTypes2ATypes fct))
 where
  callTypes2ATypes cts = let ats = map callType2AType cts
                         in if any isEmptyType ats
                              then Nothing
                              else Just (map (normalizeAType allcons) ats)

  callType2AType AnyT       = anyType
  callType2AType (MCons cs) =
    let cats = map (\(qc,cts) -> ((qc, length cts),
                                  aCons qc (map callType2AType cts))) cs
    in if isCompleteConstructorList allcons (map fst cs) &&
          all isAnyType -- are all abstract constructor arguments any type?
              (concatMap (\((qc,ar),aqc) -> argTypesOfCons qc ar aqc) cats)
        then anyType
        else foldr lubType emptyType (map snd cats)

--- Normalize an abstract type by recursively replacing complete sets of
--- constructors with `anyType` arguments by `anyType`.
--- Note that this works only for abstract values which are depth-bounded,
--- i.e., not for regular types. Thus, this operation might be better moved
--- into the implementation of a particular abstract domain.
normalizeAType :: TermDomain a => [[(QName,Int)]] -> a -> a
normalizeAType allcons at =
  let cs   = consOfType at
      cats = map (\qc -> (qc, map (normalizeAType allcons)
                              (argTypesOfCons qc 0 at))) cs
  in if null cs
       then at
       else if isCompleteConstructorList allcons cs &&
               all isAnyType -- are all constructor arguments any type?
                   (concatMap snd cats)
              then anyType
              else foldr lubType emptyType
                         (map (\(qc,ats) -> aCons qc ats) cats)

-- Describes an abstract call type a totally reducible operation?
isTotalACallType :: TermDomain a => ACallType a -> Bool
isTotalACallType Nothing    = False
isTotalACallType (Just ats) = all isAnyType ats

--- The call type of an operation which has no non-failing arguments
--- expressible by call types for the arguments.
failACallType :: TermDomain a => ACallType a
failACallType = Nothing

--- Is the call type a failure call type?
isFailACallType :: TermDomain a => ACallType a -> Bool
isFailACallType Nothing  = True
isFailACallType (Just _) = False

-- Pretty print an abstract call type for an operation.
prettyFunCallAType :: TermDomain a => ACallType a -> String
prettyFunCallAType Nothing    = "<FAILING>"
prettyFunCallAType (Just ats) = case ats of
  []   -> "()"
  [at] -> showType at
  _    -> "(" ++ intercalate ", " (map showType ats) ++ ")"

--- Join two abstract call types.
joinACallType :: TermDomain a => ACallType a -> ACallType a -> ACallType a
joinACallType Nothing     _           = Nothing
joinACallType (Just _)    Nothing     = Nothing
joinACallType (Just ats1) (Just ats2) =
  let ats = map (uncurry joinType) (zip ats1 ats2)
  in if any isEmptyType ats then Nothing
                               else Just ats

--- Is a list of abstract call types (first argument) a subtype of
--- the call type of an operation (second argument)?
subtypeOfRequiredCallType :: TermDomain a => [a] -> ACallType a -> Bool
subtypeOfRequiredCallType _   Nothing     = False
subtypeOfRequiredCallType ats (Just rats) =
  all (uncurry isSubtypeOf) (zip ats rats)
 
 --- Is an abstract type `at1` a subtype of another abstract type `at2`?
 --- Thus, are all values described by `at1` contained in the set of
 --- values described by `at2`?
isSubtypeOf :: TermDomain a => a -> a -> Bool
isSubtypeOf  at1 at2  = joinType at1 at2 == at1

------------------------------------------------------------------------------

--- Is it possible to specialize the abstract types of the given
--- argument variables so that their type is a subtype of the
--- function call type given in the second argument?
--- If yes, the specialized argument variable types are returned.
specializeToRequiredType :: TermDomain a => [(Int,a)] -> ACallType a
                         -> Maybe [(Int,a)]
specializeToRequiredType _   Nothing    = Nothing
specializeToRequiredType ats (Just cts) =
  let newtypes = map (uncurry joinType) (zip (map snd ats) cts)
  in if any isEmptyType newtypes
       then Nothing
       else Just (zip (map fst ats) newtypes)

------------------------------------------------------------------------------
