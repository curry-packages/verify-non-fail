------------------------------------------------------------------------------
--- The definition of call types and an operation to infer them.
---
--- @author Michael Hanus
--- @version June 2023
------------------------------------------------------------------------------

module Verify.CallTypes where

import Data.List

import Analysis.Values
import FlatCurry.Files
import FlatCurry.Goodies
import FlatCurry.Types

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

--- The call type of an operation which has no non-failing arguments
--- expressible by call types for the arguments.
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
prettyFunCallTypes = intercalate " | " . map prettyCallTypeArgs

prettyCallTypeArgs :: [CallType] -> String
prettyCallTypeArgs cts = case cts of
  []   -> "()"
  [ct] -> prettyCT ct
  _    -> "(" ++ intercalate "," (map prettyCT cts) ++ ")"


--- Simplify call types by recursively transforming each complete
--- list of constructors with `AnyT` arguments to `AnyT`.
simpFuncCallType :: [[QName]] -> [[CallType]] -> [[CallType]]
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
    complete2Any (c:cs)
      | all (== AnyT) (concatMap snd (c:cs)) && -- all arguments AnyT?
        maybe False
              (\qcs -> all (`elem` map fst cs) qcs)
              (getSiblingsOf allcons (fst c))
      = AnyT
      | otherwise = MCons (c:cs)


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
--- provided as the first argument.
callTypeFunc :: Options -> [[QName]] -> FuncDecl -> (QName,[[CallType]])
callTypeFunc opts allcons (Func qf ar _ _ rule) = case rule of
  External _  -> callTypeExternalFunc qf ar
  Rule vs exp -> if length vs /= ar
                   then error $ "Func " ++ show qf ++ ": inconsistent variables"
                   else (qf, simpFuncCallType allcons
                              (callTypeExpr (initCallTypeState opts qf vs) exp))

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
        LPattern lit  -> ctst { ctstCallType = addCons2CT (lit2cons lit) 0 vpos
                                                          (ctstCallType ctst) }
   where vpos = maybe (varNotFound v) id (lookup v (ctstVarPos ctst))

  addBranchPattern (Pattern _ vs) = addFreshVars vs ctst
  addBranchPattern (LPattern _)   = ctst

------------------------------------------------------------------------------

--- Transforms a call type into an abstract type.
callType2AType :: CallType -> AType
callType2AType AnyT       = Any
callType2AType (MCons qs) = ACons (nub (map fst qs))

--- Transforms a call type into an abstract type.
aType2CallType :: [[(QName,Int)]] -> AType -> CallType
aType2CallType _       Any        = AnyT
aType2CallType allcons (ACons qs) =
  MCons (map (\qc -> (qc, take (arityOfCons allcons qc) (repeat AnyT))) qs)

------------------------------------------------------------------------------

--- Is an (actual) call type a subtype of the required call types?
subtypeOfSomeAT :: [AType] -> [[CallType]] -> Bool
subtypeOfSomeAT ct cts = any (subtypesAT ct) cts
 where subtypesAT as bs = all (uncurry subtypeAT) (zip as bs)

-- Subtype relation between an abstract type and a call type.
subtypeAT :: AType -> CallType -> Bool
subtypeAT _          AnyT       = True
subtypeAT Any        (MCons _ ) = False
subtypeAT (ACons m1) (MCons m2) =
  all (\ (_,ats) -> all (==AnyT) ats) m2 -- no further argument restrictions
  && all (`elem` map fst m2) m1

------------------------------------------------------------------------------

--- Is it possible to specialize the call types of the variables so that
--- their type is a subtype of the required call type?

makeSubtypeOfSomeAT :: [(Int,AType)] -> [[CallType]] -> Maybe [(Int,AType)]
makeSubtypeOfSomeAT _  []       = Nothing
makeSubtypeOfSomeAT ats (argct:argcts) =
  maybe (makeSubtypeOfSomeAT ats argcts)
        Just
        (makeSubtypesOfCTs ats argct)
 where
  makeSubtypesOfCTs _          []       = Just []
  makeSubtypesOfCTs (vat:vats) (ct:cts) =
    maybe Nothing
          (\nvats1 -> maybe Nothing
                            (\nvats2 ->
                               let nvats = joinVarATypes (nvats1 ++ nvats2)
                               in if any ((==emptyType) . snd) nvats
                                    then Nothing
                                    else Just nvats)
                            (makeSubtypesOfCTs vats cts))
          (makeSubtypeOfCT vat ct)
  makeSubtypesOfCTs [] (_:_) = -- should not occur
    error "Internal error in 'makeSubtypeOfSomeAT': different parameters"

-- Subtype relation between an abstract type and a call type.
makeSubtypeOfCT :: (Int,AType) -> CallType -> Maybe [(Int,AType)]
makeSubtypeOfCT _          AnyT         = Just []
makeSubtypeOfCT (v,Any)    ct@(MCons _) = Just [(v, callType2AType ct)]
makeSubtypeOfCT (_,ACons m1) (MCons m2)
  | all (\ (_,ats) -> all (==AnyT) ats) m2 -- no further argument restrictions
    && all (`elem` map fst m2) m1       = Just []
  | otherwise                           = Nothing

joinVarATypes :: [(Int,AType)] -> [(Int,AType)]
joinVarATypes vats =
  map (\v -> (v, foldr joinAType anyType
                       (map snd (filter ((==v) . fst) vats))))
      (nub (map fst vats))

------------------------------------------------------------------------------
