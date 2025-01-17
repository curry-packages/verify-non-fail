-----------------------------------------------------------------------------
--- This module implements a transformation on FlatCurry programs
--- which adds `Typed` expressions to variables/function/constructor calls.
---
--- @author  Michael Hanus
--- @version January 2025
---------------------------------------------------------------------------

module FlatCurry.AddTypes
 where

import Data.List

import Control.Monad.Trans.State
import qualified Data.Map as Map
import FlatCurry.Build
import FlatCurry.Goodies
import FlatCurry.Names    ( anonCons )
import FlatCurry.Print
import FlatCurry.Read     ( readFlatCurryWithImports )
import FlatCurry.Simplify ( simpExpr )
import FlatCurry.Types

import Verify.Options     ( printInfoLine ) 
import Verify.ProgInfo

testAddTypes :: String -> IO ()
testAddTypes mname = do
  progs <- fmap (map removeTopForallType) (readFlatCurryWithImports mname)
  testAddTypesWithProgs mname (map (\p -> (progName p, prog2ModInfo p)) progs)

testAddTypesWithProgs :: String -> [(String,ModInfo)] -> IO ()
testAddTypesWithProgs mname progs = do
  let st = transInfoFrom progs defaultAddTypeOptsPoly
  printInfoLine $ showFlatProg (evalState (addTypes2Module mname) st)

addTypes2FuncDecls :: [(String,ModInfo)] -> [FuncDecl] -> [FuncDecl]
addTypes2FuncDecls modinfos fdecls =
  let st = transInfoFrom modinfos defaultAddTypeOptsPoly
  in evalState (mapM addTypes2Func fdecls) st

-- Transform a FlatCurry expression w.r.t. a given list of typed variables
-- (occurring freely in the expression) by adding type information, e.g.,
-- transform variables and combinations into `Typed` expressions.
-- The last argument is the expected result type of the expression.
addTypes2VarExp :: [(String,ModInfo)] -> [(Int,TypeExpr)] -> Expr -> TypeExpr
                -> Expr
addTypes2VarExp modinfos vartypes exp rtype =
  let st = transInfoFrom modinfos defaultAddTypeOptsPoly
  in evalState (addTypes2Rule vartypes exp rtype) st { currExp = showExp exp }

------------------------------------------------------------------------------
-- The information used during the transformation.
data TransInfo = TransInfo
  { tiOpts    :: AddTypeOpts         -- options for type annotations
  , modInfos  :: [(String,ModInfo)]  -- program infos of all modules
  , currExp   :: String              -- name or expression to be type inferred
  , freshTVar :: Int                 -- fresh type variable index
  , varTypes  :: [(Int,TypeExpr)]    -- current variables and their types
  , currSubst :: TSubst              -- current type substitution
  }

-- Option to specify where type annotations should be added.
data AddTypeOpts = AddTypeOpts
  { optAddVarType   :: Bool -- annotate variables with types?
  , optAddLitType   :: Bool -- annotate literals with types?
  , optAddCombType  :: Bool -- annotate combinations with types?
  , optAddPolyType  :: Bool -- annotate polymorphic combinations with types?
  }

-- Default options for adding types: add all types.
defaultAddTypeOptsAll :: AddTypeOpts
defaultAddTypeOptsAll = AddTypeOpts True True True True

-- Default options for adding types: add types to polymorphic combinations.
defaultAddTypeOptsPoly :: AddTypeOpts
defaultAddTypeOptsPoly = AddTypeOpts False False False True

-- Create a `TransInfo` from a list of FlatCurry programs.
transInfoFrom :: [(String,ModInfo)] -> AddTypeOpts -> TransInfo
transInfoFrom proginfos atopts =
  TransInfo atopts proginfos "" 0 [] []

-- The type of the state monad contains the transformation state.
type TransState a = State TransInfo a

-- Gets the FlatCurry program of a module with a given name.
getProgInfoFor :: String -> String -> TransState ModInfo
getProgInfoFor mn reason = do
  st <- get
  maybe (error $ "Module '" ++ mn ++ "' not found in state (required for " ++
                 reason ++ ")!")
        return
        (lookup mn (modInfos st))

-- Gets a new fresh type variable.
newFreshTVar :: TransState Int
newFreshTVar = do
  st <- get
  let tv = freshTVar st
  put st { freshTVar = tv + 1}
  return tv

-- Gets the type of a variable (which must exist!).
getVarType :: Int -> TransState TypeExpr
getVarType v = do
  st <- get
  maybe (error $ "Type inference of " ++ currExp st ++ ": variable " ++
                 show v ++ " does not exist!")
        return
        (lookup v (varTypes st))

-- Add variables and their types.
addVarTypes :: [(Int,TypeExpr)] -> TransState ()
addVarTypes vts = do
  st <- get
  put st { varTypes = vts ++ varTypes st }

-- Apply the current type substitution to a type expression.
applyCurrTSubst :: TypeExpr -> TransState TypeExpr
applyCurrTSubst texp = do
  st <- get
  return $ applyTSubst (currSubst st) texp

-- Add a binding for a type variable to the current type substitution.
addTVarBind :: Int -> TypeExpr -> TransState ()
addTVarBind tvar texp = do
  st <- get
  let bind = (tvar,texp)
  -- TODO: occur check (only as a double check since it should always fail)
  put st { currSubst = bind :
            map (\(tv,te) -> (tv, applyTSubst [bind] te)) (currSubst st) }

-- Unify the given types and add the unifier to the current substitution.
-- Newer type variables are bound to older ones in order to keep
-- a given polymorphic (function) type.
unifyTypes :: TypeExpr -> TypeExpr -> TransState ()
unifyTypes texp1 texp2 = do
  te1 <- applyCurrTSubst texp1
  te2 <- applyCurrTSubst texp2
  let typeError = do st <- get
                     error $ "Cannot unify '" ++ show te1 ++ "' and '" ++
                       show te2 ++ "'\nwhen inferring type of\n" ++ currExp st
  case te1 of
    TVar v1 -> case te2 of
                TVar v2 | v1 == v2  -> return ()
                        | v1 <  v2  -> addTVarBind v2 te1
                _                   -> addTVarBind v1 te2
    FuncType t1 t2 -> case te2 of TVar _         -> unifyTypes te2 te1
                                  FuncType s1 s2 -> do unifyTypes t1 s1
                                                       unifyTypes t2 s2
                                  _              -> typeError
    TCons qtc1 tes1 -> case te2 of
      TVar _          -> unifyTypes te2 te1
      TCons qtc2 tes2 -> if qtc1 == qtc2
                          then mapM_ (uncurry unifyTypes) (zip tes1 tes2)
                          else typeError
      _               -> typeError
    ForallType tvs1 fte1 -> case te2 of
      TVar _               -> unifyTypes te2 te1
      ForallType tvs2 fte2 -> if map snd tvs1 == map snd tvs2
                                then do mapM_ (uncurry unifyTypes)
                                              (zip (map (TVar . fst) tvs1)
                                                   (map (TVar . fst) tvs2))
                                        unifyTypes fte1 fte2
                                else typeError
      _                    -> typeError


-- Returns type-annotate expression (depending on option).
typedExp :: (AddTypeOpts -> Bool) -> Expr -> TypeExpr -> TransState Expr
typedExp addopt exp te = do
  st <- get
  return $ if addopt (tiOpts st) then addType2Exp exp te else exp

-- Adds a type to an expression if it is not already typed.
addType2Exp :: Expr -> TypeExpr -> Expr
addType2Exp exp te = case exp of Typed _ _ -> exp
                                 _         -> Typed exp te

------------------------------------------------------------------------------

-- Transform a FlatCurry program by adding type information, i.e.,
-- transform variables and combination into `Typed` expressions.
addTypes2Module :: String -> TransState Prog
addTypes2Module mn = do
  prog <- fmap miProg (getProgInfoFor mn "to get all functions")
  trfuncs <- mapM addTypes2Func (progFuncs prog)
  return $ updProgFuncs (const trfuncs) prog

-- Transform a FlatCurry function by adding type information, i.e.,
-- transform variables and combination into `Typed` expressions.
addTypes2Func :: FuncDecl -> TransState FuncDecl
addTypes2Func fd@(Func _ _ _ _ (External _)) = return fd
addTypes2Func (Func name arity vis texp (Rule args exp)) = do
  let (atypes,rtype) = splitArgTypes (length args) texp
  st <- get
  put st { currExp = snd name }
  trexp <- addTypes2Rule (zip args atypes) exp rtype
  return $ Func name arity vis texp (Rule args (simpExpr trexp))

-- Transform a rule's right-hand side w.r.t. a given list of typed
-- argument variables by adding type information, i.e.,
-- transform variables and combinations into `Typed` expressions.
-- The last argument is the expected result type of the expression.
addTypes2Rule :: [(Int,TypeExpr)] -> Expr -> TypeExpr -> TransState Expr
addTypes2Rule vartypes exp rtype = do
  let tvars = concatMap allTVarsInTExp (rtype : map snd vartypes) ++
              allTVarsInExp exp
  st <- get
  put st { freshTVar = maximum (0:tvars) + 1
         , varTypes = vartypes, currSubst = [] }
  trexp <- addTypes2Expr rtype exp
  st' <- get
  -- apply current type substitution to all Type occurrences in the expression:
  return $  applyTSubst2Exp (currSubst st') trexp

-- Transform a FlatCurry expression by adding type information, i.e.,
-- transform variables and combination into `Typed` expressions.
addTypes2Expr :: TypeExpr -> Expr -> TransState Expr
addTypes2Expr = addTypes
 where
  addTypes te exp = case exp of
    Var  v          -> do vt <- getVarType v
                          unifyTypes vt te
                          typedExp optAddVarType exp te
    Lit  lit        -> do unifyTypes (litType lit) te
                          typedExp optAddLitType exp te
    Comb FuncCall qf [e1,e2] | qf `elem` map pre ["==", ">="]
      -- special handling of primitive operations as introduced in assertions
      -> do tv <- newFreshTVar    
            targs <- mapM (addTypes (TVar tv)) [e1, e2]
            typedExp optAddCombType (Comb FuncCall qf targs) fcBool
    Comb ct qf args -> do qfte <- getCombTypeOf ct qf >>= freshTypeVariant
                          let ispoly = not (null (allTVarsInTExp qfte))
                          let (ats,rt) = splitArgTypes (length args) qfte
                          unifyTypes rt te
                          targs <- mapM (uncurry addTypes) (zip ats args)
                          st <- get
                          if ispoly && optAddPolyType (tiOpts st)
                            then return $
                              Typed (Comb ct qf (map (uncurry addType2Exp)
                                                     (zip targs ats))) te
                            else typedExp optAddCombType (Comb ct qf targs) te
    Let  bs e       -> do bts <- mapM (\_ -> newFreshTVar >>= return . TVar) bs
                          addVarTypes (zip (map fst bs) bts)
                          trbexps <- mapM (uncurry addTypes)
                                          (zip bts (map snd bs))
                          tre <- addTypes te e
                          return $ Let (zip (map fst bs) trbexps) tre
    Or   e1 e2      -> do tre1 <- addTypes te e1
                          tre2 <- addTypes te e2
                          return $ Or tre1 tre2
    Case ct e brs   -> do ctv <- fmap TVar newFreshTVar
                          tre <- addTypes ctv e
                          trbrs <- mapM (addTypesBranch ctv te) brs
                          return $ Case ct tre trbrs
    Typed e tte     -> do trexp <- addTypes tte e
                          unifyTypes tte te
                          return $ Typed trexp tte
    Free vs e       -> do vts <- mapM (\v -> newFreshTVar >>=
                                       \tv -> return (v, TVar tv)) vs
                          addVarTypes vts
                          trexp <- addTypes te e
                          return $ Free vs trexp

  addTypesBranch ptype te (Branch pat@(Pattern qc pvs) e)
    | qc == anonCons
    = do tre <- addTypes te e
         return $ Branch pat tre
    | otherwise
    = do qfte  <- getConsTypeOf qc >>= freshTypeVariant
         let (ats,rt) = splitArgTypes (length pvs) qfte
         unifyTypes rt ptype
         addVarTypes (zip pvs ats)
         tre <- addTypes te e
         return $ Branch pat tre
  addTypesBranch ptype te (Branch pat@(LPattern lit) e) = do
    unifyTypes ptype (litType lit)
    tre <- addTypes te e
    return $ Branch pat tre

  litType (Intc   _) = fcInt
  litType (Floatc _) = fcFloat
  litType (Charc  _) = fcChar

--- Splits a possibly functional type into types of arguments and result
--- w.r.t. a given arity.
splitArgTypes :: Int -> TypeExpr -> ([TypeExpr],TypeExpr)
splitArgTypes ar te
  | ar == 0
  = ([],te)
  | otherwise
  = case te of
      FuncType dom ran -> let (ats,rt) = splitArgTypes (ar-1) ran
                          in (dom : ats, rt)
      ForallType _ fte -> splitArgTypes ar fte
      _                -> error $ "Cannot strip argument types from " ++ show te

-- Transforms a type expression into a variant with new type variables.
freshTypeVariant :: TypeExpr -> TransState TypeExpr
freshTypeVariant te = do
  let tevs = nub (allTVarsInTExp te)
  newtevs <- mapM (\_ -> newFreshTVar) tevs
  let rnm i = maybe i id (lookup i (zip tevs newtevs))
  return $ rnmTVar rnm te
 where
  rnmTVar rnm texp = case texp of
    TVar i           -> TVar (rnm i)
    FuncType te1 te2 -> FuncType (rnmTVar rnm te1) (rnmTVar rnm te2)
    TCons tc texps   -> TCons tc (map (rnmTVar rnm) texps)
    ForallType tvs t -> ForallType (map (\(tv,kd) -> (rnm tv, kd)) tvs)
                                   (rnmTVar rnm t)

-- Gets the type of a qualified name occurring in a combination.
getCombTypeOf :: CombType -> QName -> TransState TypeExpr
getCombTypeOf ct = case ct of FuncCall       -> getFuncTypeOf
                              FuncPartCall _ -> getFuncTypeOf
                              ConsCall       -> getConsTypeOf
                              ConsPartCall _ -> getConsTypeOf

-- Gets the type of a qualified function name.
getFuncTypeOf :: QName -> TransState TypeExpr
getFuncTypeOf qc@(mn,fn)
  | qc == pre "failed" = return (TVar 1)
  | otherwise
  = do pi <- getProgInfoFor mn ("function " ++ fn)
       maybe (error $ "Function '" ++ fn ++ "' not found in state!")
             return
             (Map.lookup fn (miFTypes pi))

-- Gets the type of a qualified constructor name.
getConsTypeOf :: QName -> TransState TypeExpr
getConsTypeOf qc@(mn,fn)
  | qc `elem` map pre ["False", "True"] = return fcBool
  | qc == pre "[]" = return $ fcList (TVar 0)
  | qc == pre ":"  = return $ FuncType (TVar 0) (FuncType (fcList (TVar 0))
                                                          (fcList (TVar 0)))
  | otherwise
  = do pi <- getProgInfoFor mn ("constructor " ++ fn)
       maybe (error $ "Constructor '" ++ fn ++ "' not found in state!")
             (\(_,ConsType tes tc tvs,_) ->
               return $ foldr FuncType (TCons tc (map TVar tvs)) tes)
             (Map.lookup fn (miCInfos pi))

------------------------------------------------------------------------------
-- A type substitution is a mapping from type variables to type expressions.
type TSubst = [(Int,TypeExpr)]

-- Apply a type substitution to a type expression.
applyTSubst :: TSubst -> TypeExpr -> TypeExpr
applyTSubst ts texp = case texp of
  TVar v            -> maybe (TVar v) id (lookup v ts)
  FuncType t1 t2    -> FuncType (applyTSubst ts t1) (applyTSubst ts t2)
  TCons qtc tes     -> TCons qtc (map (applyTSubst ts) tes)
  ForallType tvs te -> ForallType tvs (applyTSubst ts te) --TODO: tvs

-- Apply a type substitution to all types occurring in an expression.
applyTSubst2Exp :: TSubst -> Expr -> Expr
applyTSubst2Exp ts = updTypeds (\e te -> Typed e (applyTSubst ts te))

------------------------------------------------------------------------------
-- Get all type variables occurring in a function declaration.
allTVarsInFuncDecl :: FuncDecl -> [Int]
allTVarsInFuncDecl (Func _ _ _ texp rule) =
  allTVarsInTExp texp ++ allTVarsInRule rule
 where
  allTVarsInRule (Rule _ exp) = allTVarsInExp exp
  allTVarsInRule (External _) = []

-- Get all type variables in a type expression.
allTVarsInTExp :: TypeExpr -> [Int]
allTVarsInTExp te = trTypeExpr (:) tcomb (.) forall te []
 where
  tcomb _ = foldr (.) id
  forall tvs texp = (map fst tvs ++) . texp

-- Get all type variables occurring in an expression.
allTVarsInExp :: Expr -> [Int]
allTVarsInExp e = trExpr (const id) (const id) comb lt fr (.) cas branch fre e []
 where
  comb _ _ = foldr (.) id
  lt bs exp = exp . foldr (.) id (map snd bs)
  fr _ exp = exp
  cas _ exp bs = exp . foldr (.) id bs
  branch _ exp = exp
  fre exp te = (allTVarsInTExp te ++) . exp

allTVarsInTDecl :: TypeDecl -> [Int]
allTVarsInTDecl (Type _ _ tvars _) = map fst tvars
allTVarsInTDecl (TypeSyn _ _ tvars _) = map fst tvars
allTVarsInTDecl (TypeNew _ _ tvars _) = map fst tvars

------------------------------------------------------------------------------
