-------------------------------------------------------------------------
--- A tool to verify Curry programs w.r.t. failing computations.
--- Thus, a program successfully verified by this tool should never
--- fail at run-time (apart from explicit error) provided that
--- the call types are satisfied when invoking a function.
---
--- @author Michael Hanus
--- @version October 2023
-------------------------------------------------------------------------

module Main where

import Control.Monad              ( unless, when )
import Data.List
import System.Environment         ( getArgs )

import Debug.Trace ( trace )

-- Imports from dependencies:
import Analysis.Types             ( Analysis, analysisName )
--import Analysis.TermDomain
import Control.Monad.Trans.Class  ( lift )
import Control.Monad.Trans.State  ( StateT, get, put, execStateT )
import Data.IORef
import qualified Data.Map as Map
import Debug.Profile
import FlatCurry.Files
import FlatCurry.Goodies
import FlatCurry.NormalizeLet
import qualified FlatCurry.Pretty as FCP
import FlatCurry.Types
import System.CurryPath           ( runModuleAction )
import System.Directory           ( createDirectoryIfMissing, doesFileExist
                                  , removeDirectory )
import System.FilePath            ( (</>) )
import Text.Pretty                ( Doc, (<+>), align, pPrint, text )

-- Imports from package modules:
import Verify.CallTypes
import Verify.Domain
import Verify.Files
import Verify.Helpers
import Verify.IOTypes
import Verify.Options
import Verify.Statistics

------------------------------------------------------------------------------
banner :: String
banner = unlines [bannerLine, bannerText, bannerLine]
 where
  bannerText = "Curry Call Pattern Verifier (Version of 24/10/23)"
  bannerLine = take (length bannerText) (repeat '=')

main :: IO ()
main = do
  args <- getArgs
  (opts',progs) <- processOptions banner args
  let opts = opts' { optDomainID = analysisName valueAnalysis }
  when (optDeleteCache opts) $ deleteVerifyCacheDirectory opts
  case progs of
    [] -> unless (optDeleteCache opts) $ error "Module name missing"
    ms -> do astore <- newIORef (AnaStore [])
             mapM_ (runModuleAction (verifyModule astore opts)) ms

-- compatibility definitions for the moment:
type VarType = Verify.IOTypes.VarType AType
type InOutType = Verify.IOTypes.InOutType AType
type ACallType = Verify.CallTypes.ACallType AType


--- Verify a single module.
verifyModule :: IORef (AnalysisStore AType) -> Options -> String -> IO ()
verifyModule astore opts mname = do
  printWhenStatus opts $ "Processing module '" ++ mname ++ "':"
  mtime    <- getModuleModTime mname
  flatprog <- readFlatCurry mname >>= return . transformChoiceInProg
  let fdecls   = progFuncs flatprog
      visfuncs = map funcName (filter ((== Public) . funcVisibility) fdecls)
  imps@(impconss,impacalltypes,impiotypes) <-
    if optImports opts
      then do
        whenStatus opts $ putStr $
          "Reading abstract types of imports: " ++ unwords (progImports flatprog)
        readTypesOfModules opts (verifyModule astore) (progImports flatprog)
      else return ([],[],[])
  if optTime opts then do whenStatus opts $ putStr "..."
                          (id $## imps) `seq` printWhenStatus opts "done"
                  else printWhenStatus opts ""
  let allcons = allConsOfTypes (progTypes flatprog) ++ impconss
  oldpubcalltypes <- readPublicCallTypeModule opts allcons mtime mname
  let calltypes    = unionBy (\x y -> fst x == fst y) oldpubcalltypes
                             (map (callTypeFunc opts allcons) fdecls)
      ntcalltypes  = filter (not . isTotalCallType . snd) calltypes
      pubcalltypes = filter ((`elem` visfuncs) . fst) ntcalltypes
  if optVerb opts > 2
    then putStrLn $ unlines $ "CONCRETE CALL TYPES OF ALL OPERATIONS:" :
           showFunResults prettyFunCallTypes calltypes
    else when (optVerb opts > 1 || optCallTypes opts) $
      putStrLn $ unlines $
        ("NON-TRIVIAL CONCRETE CALL TYPES OF " ++
         (if optPublic opts then "PUBLIC" else "ALL") ++ " OPERATIONS:") :
        showFunResults prettyFunCallTypes
         (sortFunResults (if optPublic opts then pubcalltypes else ntcalltypes))

  mboldacalltypes <- readCallTypeFile opts mtime mname
  let pubmodacalltypes = map (funcCallType2AType allcons) oldpubcalltypes
      acalltypes = unionBy (\x y -> fst x == fst y) pubmodacalltypes
                           (maybe (map (funcCallType2AType allcons) calltypes)
                                  id
                                  mboldacalltypes)
      ntacalltypes  = filter (not . isTotalACallType . snd) acalltypes
      pubacalltypes = filter ((`elem` visfuncs) . fst) ntacalltypes
  if optVerb opts > 2
    then putStrLn $ unlines $ "ABSTRACT CALL TYPES OF ALL OPERATIONS:" :
           showFunResults prettyFunCallAType acalltypes
    else when (optVerb opts > 1 || optCallTypes opts) $
      putStrLn $ unlines $
        ("NON-TRIVIAL ABSTRACT CALL TYPES OF " ++
         (if optPublic opts then "PUBLIC" else "ALL") ++ " OPERATIONS:") :
        showFunResults prettyFunCallAType
          (sortFunResults $ if optPublic opts then pubacalltypes
                                              else ntacalltypes)

  rvmap <- loadAnalysisWithImports astore valueAnalysis opts flatprog
  let iotypes      = map (inOutATypeFunc rvmap) fdecls
      ntiotypes    = filter (not . isAnyIOType . snd) iotypes
      pubntiotypes = filter ((`elem` visfuncs) . fst) ntiotypes
  if optVerb opts > 2
    then putStrLn $ unlines $ "INPUT/OUTPUT TYPES OF ALL OPERATIONS:" :
           showFunResults showIOT iotypes
    else when (optVerb opts > 1 || optIOTypes opts) $
      putStrLn $ unlines $
        ("NON-TRIVIAL INPUT/OUTPUT TYPES OF " ++
         (if optPublic opts then "PUBLIC" else "ALL") ++ " OPERATIONS:") :
        showFunResults showIOT
          (sortFunResults (if optPublic opts then pubntiotypes else ntiotypes))

  let vstate = initVerifyState fdecls allcons (Map.fromList impacalltypes)
                               (Map.fromList acalltypes)
                               (Map.fromList (iotypes ++ impiotypes)) opts
      funusage = funcDecls2Usage mname (progFuncs flatprog)
  printWhenAll opts $ unlines $
    ("Function usage in module '" ++ mname ++ "':") :
    map (\ (qf, qfs) -> snd qf ++ ": used in " ++
                        unwords (map (snd . funcName) qfs))
        (Map.toList funusage)
  (vnumits, vtime, vst) <-
   if optVerify opts
     then do
       printWhenStatus opts $ "Start verification of '" ++ mname ++ "' (" ++
         show (length fdecls) ++ " functions):"
       pi1 <- getProcessInfos
       (numits,st) <- tryVerifyProg opts 0 vstate mname funusage fdecls
       pi2 <- getProcessInfos
       showVerifyResult opts st mname fdecls
       let tdiff = maybe 0 id (lookup ElapsedTime pi2) -
                   maybe 0 id (lookup ElapsedTime pi1)
       when (optTime opts) $ putStrLn $
         "TOTAL VERIFICATION TIME: " ++ show tdiff ++ " msec"
       return (numits, tdiff, st)
     else return (0, 0, vstate)
  -- print statistics:
  let finalacalltypes   = Map.toList (vstCallTypes vst)
      finalntacalltypes = filter (not . isTotalACallType . snd) finalacalltypes
      (stattxt,statcsv) = showStatistics opts vtime vnumits visfuncs
                            (length fdecls)
                            (length pubntiotypes, length ntiotypes)
                            (length pubacalltypes, length ntacalltypes)
                            finalntacalltypes (vstStats vst)
  when (optStats opts) $ putStr stattxt
  when (optVerify opts) $ do
    storeTypes opts mname (allConsOfTypes (progTypes flatprog))
               finalacalltypes iotypes
    storeStatistics opts mname stattxt statcsv
  unless (null (optFunction opts)) $ showFunctionInfo opts mname vst

showFunctionInfo :: Options -> String -> VerifyState -> IO ()
showFunctionInfo opts mname vst = do
  let f = optFunction opts
      qf = (mname, f)
  if qf `notElem` map funcName (vstFuncDecls vst)
    then putStrLn $ "Function '" ++ snd qf ++ "' not defined!"
    else do
      let ctype = maybe (Just [anyType]) id (Map.lookup qf (vstCallTypes vst))
          iot   = maybe (trivialInOutType 0) id (Map.lookup qf (vstIOTypes vst))
      putStrLn $ "Function '" ++ f ++ "':"
      putStrLn $ "Call type  : " ++ prettyFunCallAType ctype
      putStrLn $ "In/out type: " ++ showIOT iot

-- Try to verify a module, possibly in several iterations.
-- The second argument is the number of already performed iterations,
-- the first component of the result is the total number of iterations.
tryVerifyProg :: Options -> Int -> VerifyState -> String
              -> Map.Map QName [FuncDecl] -> [FuncDecl] -> IO (Int,VerifyState)
tryVerifyProg opts numits vstate mname funusage fdecls = do
  st <- execStateT (mapM_ verifyFunc fdecls) vstate
  let newfailures = vstNewFailed st
  unless (null newfailures || optVerb opts < 2) $ printFailures st
  unless (null newfailures) $ printWhenStatus opts $ unlines $
    "Operations with refined call types (used in future analyses):" :
    showFunResults prettyFunCallAType (reverse newfailures)
  let st' = st { vstCallTypes = Map.union (Map.fromList newfailures)
                                          (vstCallTypes st)
               , vstNewFailed = [] }
  if null newfailures
    then do printFailures st'
            return (numits + 1, st')
    else do
      let -- functions with refined call types:
          rfuns = map fst (filter (not . isFailACallType . snd) newfailures)
          newfdecls =
            foldr unionFDecls
              (filter (\fd -> funcName fd `elem` rfuns) (vstFuncDecls st))
              (map (\ (qf,_) -> maybe [] id (Map.lookup qf funusage))
                   newfailures)
      printWhenStatus opts $ "Repeat verification with new call types..." ++
        "(" ++ show (length newfdecls) ++ " functions)"
      --putStrLn $ unlines $
      --  showFunResults prettyFunCallAType (sortFunResults $ vstCallTypes st')
      tryVerifyProg opts (numits + 1) st' mname funusage newfdecls
 where
  failLine = take 78 (repeat '!')
  failComment = failLine ++ "\nPROGRAM CONTAINS POSSIBLY FAILING "

  printFailures st = do
    unless (null (vstFailedFuncs st)) $
      putStrLn $ failComment ++ "FUNCTION CALLS:\n" ++
         unlines (map (\ (qf,_,e) -> "Function '" ++ snd qf ++
                                     "': call '" ++ showExp e ++ "'")
                      (reverse (vstFailedFuncs st)) ++ [failLine])
    unless (null (vstPartialBranches st)) $
      putStrLn $ failComment ++ "FUNCTIONS:\n" ++
         unlines
           (map (\ (qf,_,e,cs) -> showIncompleteBranch qf e cs)
                (reverse (vstPartialBranches st)) ++ [failLine])

showVerifyResult :: Options -> VerifyState -> String -> [FuncDecl] -> IO ()
showVerifyResult opts vst mname fdecls = do
  putStr $ "MODULE '" ++ mname ++ "' VERIFIED"
  let calltypes = filter (\ (qf,ct) -> not (isTotalACallType ct) && showFun qf)
                            (Map.toList (vstCallTypes vst))
  if null calltypes || optVerb opts == 0
    then putStrLn "\n"
    else putStrLn $ unlines $ " W.R.T. NON-TRIVIAL ABSTRACT CALL TYPES:"
           : showFunResults prettyFunCallAType (sortFunResults calltypes)
 where
  showFun qf = not (optPublic opts) || qf `elem` visfuncs

  visfuncs = map funcName (filter ((== Public) . funcVisibility) fdecls)

-- Shows a message about an incomplete branch.
-- If the third argument is the empty list, it is a literal branch.
showIncompleteBranch :: QName -> Expr -> [QName] -> String
showIncompleteBranch qf e cs@(_:_) =
  "Function '" ++ snd qf ++ "': the constructor" ++
  (if length cs > 1 then "s" else "") ++ " '" ++
  unwords (map snd cs) ++ "' " ++
  (if length cs > 1 then "are" else "is") ++ " not covered in:\n" ++
  showExp e
showIncompleteBranch qf e [] =
  "Function '" ++ snd qf ++ "': the case on literals might be incomplete:\n" ++
  showExp e

------------------------------------------------------------------------------
-- The state of the transformation process contains
-- * the list of all function declarations of the current module
-- * the current function to be analyzed (name, arity, rule arguments)
-- * a list of all constructors grouped by types
-- * a fresh variable index
-- * a list of all variables and their bound expressions
-- * a list of all variables and their input/output types
-- * the call types of all operations
-- * the input/output types of all operations
-- * the list of failed function calls
-- * the list of incomplete case expressions
-- * the list of functions marked as failing in this iteration
-- * some statistics
-- * the tool options
data VerifyState = VerifyState
  { vstFuncDecls   :: [FuncDecl]        -- all function declarations of module
  , vstCurrFunc    :: (QName,Int,[Int]) -- the name/arity/args of current func.
  , vstAllCons     :: [[(QName,Int)]]   -- all constructors grouped by types
  , vstFreshVar    :: Int               -- fresh variable index in a rule
  , vstVarExp      :: [(Int,Expr)]      -- map variable to its subexpression
  , vstVarTypes    :: [VarType]         -- map variable to its abstract types
  , vstImpCallTypes:: Map.Map QName ACallType -- abstract call types of imports
  , vstCallTypes   :: Map.Map QName ACallType -- abstract call types of module
  , vstIOTypes     :: Map.Map QName InOutType -- the in/out type for all funcs
  , vstFailedFuncs :: [(QName,Int,Expr)]   -- functions with illegal calls
  , vstPartialBranches :: [(QName,Int,Expr,[QName])] -- incomplete branches
  , vstNewFailed   :: [(QName,ACallType)] -- new failed function call types
  , vstStats       :: (Int,Int) -- numbers: non-trivial calls / incomplete cases
  , vstToolOpts    :: Options
  }

--- Initializes the verification state.
initVerifyState :: [FuncDecl] -> [[(QName,Int)]]
                -> Map.Map QName ACallType -> Map.Map QName ACallType
                -> Map.Map QName InOutType -> Options
                -> VerifyState
initVerifyState fdecls allcons impacalltypes acalltypes ftypes opts =
  VerifyState fdecls (("",""),0,[]) allcons 0 [] []
              impacalltypes acalltypes ftypes [] [] [] (0,0) opts

-- The type of the state monad contains the verification state.
--type TransStateM a = State TransState a
type VerifyStateM a = StateT VerifyState IO a

-- Gets the name of the current function in the state.
getCurrentFuncName :: VerifyStateM QName
getCurrentFuncName = do
  st <- get
  return $ let (qf,_,_) = vstCurrFunc st in qf

-- Sets the name and arity of the current function in the state.
setCurrentFunc :: QName -> Int -> [Int] -> VerifyStateM ()
setCurrentFunc qf ar vs = do
  st <- get
  put $ st { vstCurrFunc = (qf,ar,vs) }

-- Gets all constructors grouped by types.
getAllCons :: VerifyStateM [[(QName,Int)]]
getAllCons = get >>= return . vstAllCons

-- Gets the current fresh variable index of the state.
getFreshVarIndex :: VerifyStateM Int
getFreshVarIndex = get >>= return . vstFreshVar

-- Sets the fresh variable index in the state.
setFreshVarIndex :: Int -> VerifyStateM ()
setFreshVarIndex fvi = do
  st <- get
  put $ st { vstFreshVar = fvi }

-- Gets a new fresh variable index.
newFreshVarIndex :: VerifyStateM Int
newFreshVarIndex = do
  v <- getFreshVarIndex
  setFreshVarIndex (v + 1)
  return v

-- Adds a new (more restricted) inferred call type for a function
-- which will be used in the next iteration. If there is already
-- a more restricted call type, they will be joined.
addCallTypeRestriction :: QName -> ACallType -> VerifyStateM ()
addCallTypeRestriction qf ctype = do
  st <- get
  maybe (put $ st { vstNewFailed = (qf,ctype) : (vstNewFailed st) } )
        (\ct -> do
           let newct = joinACallType ct ctype
           put $ st { vstNewFailed = unionBy (\x y -> fst x == fst y)
                                             [(qf,newct)] (vstNewFailed st) })
        (lookup qf (vstNewFailed st))

-- Adds a failed function call (represented by the FlatCurry expression)
-- to the current function. If the second argument is `Just vts`, then
-- this call is not failed provided that it can be ensured that the
-- variable types `vts` hold. This information is used to refine the
-- call type of the current function, if possible.
addFailedFunc :: Expr -> Maybe [(Int,AType)] -> VerifyStateM ()
addFailedFunc exp mbvts = do
  st <- get
  let (qf,ar,args) = vstCurrFunc st
  put $ st { vstFailedFuncs = union [(qf,ar,exp)] (vstFailedFuncs st) }
  maybe (addCallTypeRestriction qf failACallType)
        (\vts ->
           if any ((`elem` args) . fst) vts
             then do
               oldct <- getCallType qf ar
               let ncts  = map (\v -> maybe anyType id (lookup v vts)) args
                   newct = maybe Nothing
                                 (\oldcts -> Just (map (uncurry joinType)
                                                       (zip oldcts ncts)))
                                 oldct
               if oldct == newct
                 then noRefinementFor qf
                 else do
                   printIfVerb 2 $ "TRY TO REFINE FUNCTION CALL TYPE OF " ++
                                   snd qf ++ " TO: " ++ prettyFunCallAType newct
               addCallTypeRestriction qf newct
             else noRefinementFor qf
        )
        mbvts
 where
  noRefinementFor qf = do
    printIfVerb 2 $ "CANNOT REFINE CALL TYPE OF FUNCTION " ++ snd qf
    addCallTypeRestriction qf failACallType

-- Adds an info about cases with missing branches in the current function.
addMissingCase :: Expr -> [QName] -> VerifyStateM ()
addMissingCase exp qcs = do
  st <- get
  let (qf,ar,_) = vstCurrFunc st
  put $
    st { vstPartialBranches = union [(qf,ar,exp,qcs)] (vstPartialBranches st) }
  addCallTypeRestriction qf failACallType

-- Set the expressions for variables.
setVarExps :: [(Int,Expr)] -> VerifyStateM ()
setVarExps varexps = do
  st <- get
  put $ st { vstVarExp = varexps }

-- Adds expressions for new variables.
addVarExps :: [(Int,Expr)] -> VerifyStateM ()
addVarExps varexps = do
  st <- get
  put $ st { vstVarExp = vstVarExp st ++ varexps }

-- Get all currently stored variable types.
getVarTypes :: VerifyStateM [VarType]
getVarTypes = do
  st <- get
  return $ vstVarTypes st

-- Gets the currently stored types for a given variable.
getVarTypesOf :: Int -> VerifyStateM [VarType]
getVarTypesOf v = do
  st <- get
  return $ filter ((==v) . fst3) (vstVarTypes st)

-- Sets all variable types.
setVarTypes :: [VarType] -> VerifyStateM ()
setVarTypes vartypes = do
  st <- get
  put $ st { vstVarTypes = vartypes }

-- Adds a new variable type to the current set of variable types.
-- It could be an alternative type for an already existent variable or
-- a type for a new variable.
addVarType :: VarType -> VerifyStateM ()
addVarType vartype = do
  st <- get
  put $ st { vstVarTypes = vstVarTypes st ++ [vartype] }

-- Adds a new variable `Any` type to the current set of variable types.
addVarAnyType :: Int -> VerifyStateM ()
addVarAnyType v = addVarType (ioVarType v anyType)

-- Removes an `Any` type for a given variable from the current
-- set of variable types.
-- Used to remove the initial `Any` types in let bindings.
removeVarAnyType :: Int -> VerifyStateM ()
removeVarAnyType v = do
  st <- get
  put $ st { vstVarTypes = filter (not . isAnyTypeForV) (vstVarTypes st) }
 where
  isAnyTypeForV (var,vt,vs) = var == v &&
    case (vt,vs) of (IOT [([], at)], []) -> at == anyType
                    _                    -> False

-- Gets the abstract call type for a given operation.
-- The trivial abstract call type is returned for encapsulated search operations.
getCallType :: QName -> Int -> VerifyStateM ACallType
getCallType qf ar
  | isEncSearchOp qf || isSetFunOp qf
  = return trivialACallType
  | otherwise
  = do
  st <- get
  return $ maybe
    (maybe (trace ("Warning: call type of operation " ++ show qf ++
                   " not found!") trivialACallType)
           id
           (Map.lookup qf (vstImpCallTypes st)))
    id
    (Map.lookup qf (vstCallTypes st))
 where
  trivialACallType = Just $ take ar (repeat anyType)

-- Gets the in/out type for an operation of a given arity.
-- If the operation is not found, returns a general type.
-- The trivial in/out type is returned for encapsulated search operations.
getFuncType :: QName -> Int -> VerifyStateM InOutType
getFuncType qf ar
  | isEncSearchOp qf || isSetFunOp qf
  = return $ trivialInOutType ar
  | otherwise
  = do st <- get
       maybe (do lift $ putStrLn $
                   "WARNING: in/out type of '" ++ show qf ++ "' not found!"
                 return $ trivialInOutType ar)
             return
             (Map.lookup qf (vstIOTypes st))

-- Increment number of non-trivial calls.
incrNonTrivialCall :: VerifyStateM ()
incrNonTrivialCall = do
  st <- get
  put $ st { vstStats = (\ (f,c) -> (f+1,c)) (vstStats st) }

-- Increment number of incomplete case expressions.
incrIncompleteCases :: VerifyStateM ()
incrIncompleteCases = do
  st <- get
  put $ st { vstStats = (\ (f,c) -> (f,c+1)) (vstStats st) }

-- Gets the tool options from the current state.
getToolOptions :: VerifyStateM Options
getToolOptions = get >>= return . vstToolOpts

--- Prints a string with `putStrLn` if the verbosity is at least as the given
--- one.
printIfVerb :: Int -> String -> VerifyStateM ()
printIfVerb v s = do
  opts <- getToolOptions
  when (optVerb opts >= v) $ lift $ putStrLn s

------------------------------------------------------------------------------

-- Verify a FlatCurry function declaration.
verifyFunc :: FuncDecl -> VerifyStateM ()
verifyFunc (Func qf ar _ _ rule) = case rule of
  Rule vs exp -> unless (qf `elem` noVerifyFunctions) $ do
                   setCurrentFunc qf ar vs
                   verifyFuncRule vs (normalizeLet exp)
  External _  -> return ()

-- A list of operations that do not need to be verified.
-- These are operations that are non-failing but this property
-- cannot be ensured by the current tool.
noVerifyFunctions :: [QName]
noVerifyFunctions =
  [ pre "aValueChar" -- is non-failing if minBound <= maxBound, which is True
  ]

verifyFuncRule :: [Int] -> Expr -> VerifyStateM ()
verifyFuncRule vs exp = do
  setFreshVarIndex (maximum (0 : vs ++ allVars exp) + 1)
  setVarExps  (map (\v -> (v, Var v)) vs)
  qf <- getCurrentFuncName
  printIfVerb 2 $ "CHECKING FUNCTION " ++ snd qf
  ctype <- getCallType qf (length vs)
  maybe (printIfVerb 2 $ "not checked since marked as always failing")
        (\atargs -> do
           setVarTypes (map (\(v,at) -> (v, IOT [([],at)], [])) (zip vs atargs))
           showVarExpTypes
           verifyExpr True exp
           return ())
        ctype
  printIfVerb 2 $ take 70 (repeat '-')

-- Shows the current variable expressions and types if verbosity > 2.
showVarExpTypes :: VerifyStateM ()
showVarExpTypes = do
  qf <- getCurrentFuncName
  opts <- getToolOptions
  when (optVerb opts > 2) $ do
    st <- get
    lift $ putStr $ "Current set of variables in function " ++ snd qf ++
                    ":\nVariable bindings:\n" ++
                    unlines (map (\ (v,e) -> showBindExp v e) (vstVarExp st))
    vartypes <- getVarTypes
    lift $ putStr $ "Variable types\n" ++ showVarTypes vartypes

-- Shows a pretty-printed variable binding to a FlatCurry expression.
showBindExp :: Int -> Expr -> String
showBindExp bv e = pPrint $ text ('v' : show bv ++ " |-> ") <+> align (ppExp e)

-- Shows a pretty-printed FlatCurry expression.
showExp :: Expr -> String
showExp e = pPrint (ppExp e)

-- Pretty prints a FlatCurry expression.
ppExp :: Expr -> Doc
ppExp e = FCP.ppExp FCP.defaultOptions { FCP.qualMode = FCP.QualNone} e

-- Verify an expression (if the first argument is `True`) and,
-- if the expression is not a variable, create a fresh
-- variable and a binding for this variable.
-- The variable which identifies the expression is returned.
verifyExpr :: Bool -> Expr -> VerifyStateM Int
verifyExpr verifyexp exp = case exp of
  Var v -> do iots <- if verifyexp then verifyVarExpr v exp
                                   else return [(v, IOT [([], anyType)], [])]
              mapM addVarType iots
              return v
  _     -> do v <- newFreshVarIndex
              addVarExps [(v,exp)]
              iots <- if verifyexp then verifyVarExpr v exp
                                   else return [(v, IOT [([], anyType)], [])]
              mapM addVarType iots
              return v

-- Verify an expression identified by variable (first argument).
-- The in/out variable types collected for the variable are returned.
verifyVarExpr :: Int -> Expr -> VerifyStateM [VarType]
verifyVarExpr ve exp = case exp of
  Var v         -> if v == ve
                     then return []
                     else do
                       --lift $ putStrLn $ "Expression with different vars: " ++
                       --                  show (v,ve)
                       --showVarExpTypes
                       vtypes <- getVarTypesOf v
                       -- TODO: improve by handling equality constraint v==ve
                       -- instead of copying the current types for v to ve:
                       return $ map (\ (_,iots,vs) -> (ve,iots,vs)) vtypes
  Lit l         -> return [(ve, IOT [([], aLit l)], [])]
  Comb ct qf es -> do
    vs <- if isEncSearchOp qf
            then -- for encapsulated search, failures in arguments are hidden
                 mapM (verifyExpr False) es
            else if isSetFunOp qf
                   then -- for a set function, the function argument is hidden
                        mapM (\ (i,e) -> verifyExpr (i>0) e)
                             (zip [0..] es)
                   else mapM (verifyExpr True) es
    case ct of
      FuncCall -> do opts <- getToolOptions
                     verifyFuncCall (optError opts) exp qf vs
                     ftype <- getFuncType qf (length vs)
                     return [(ve, ftype, vs)]
      FuncPartCall n -> -- note: also partial calls are considered as constr.
                  do ctype <- getCallType qf (n + length es)
                     unless (isTotalACallType ctype) $ do
                       printIfVerb 2 $ "UNSATISFIED CALL TYPE: " ++
                         "partial application of non-total function\n"
                       addFailedFunc exp Nothing
                     -- note: also partial calls are considered as constructors
                     returnConsIOType qf vs ve
      _        -> returnConsIOType qf vs ve
  Let bs e      -> do addVarExps bs
                      mapM_ (addVarAnyType . fst) bs
                      iotss <- mapM (\ (v,be) -> verifyVarExpr v be) bs
                      -- remove initially set anyType's for the bound vars:
                      mapM_ (removeVarAnyType . fst) bs
                      mapM_ addVarType (concat iotss)
                      mapM_ (addAnyTypeIfUnknown . fst) bs
                      verifyVarExpr ve e
  Free vs e     -> do addVarExps (map (\v -> (v, Var v)) vs)
                      mapM_ addVarAnyType vs
                      verifyVarExpr ve e
  Or e1 e2      -> do iots1 <- verifyVarExpr ve e1 -- 
                      iots2 <- verifyVarExpr ve e2
                      return (iots1 ++ iots2)
  Case _ ce bs  -> do cv <- verifyExpr True ce
                      verifyMissingBranches exp cv bs
                      iotss <- mapM (verifyBranch cv ve) bs
                      return (concat iotss)
  Typed e _     -> verifyVarExpr ve e -- TODO: use type info
 where
  -- adds Any type for a variable if it is unknown
  addAnyTypeIfUnknown v = do
    vts <- getVarTypesOf v
    when (null vts) (addVarAnyType v)

  -- Return an input/output type for a constructor and its arguments
  returnConsIOType qc vs rv = do
    vts <- getVarTypes
    let vstypes = map (flip getVarType vts) vs
    --let anys = anyTypes (length vs)  -- TODO: use vs types from VarTypes!!!!
    --return [(rv, IOT [(anys, aCons qc anys)], vs)]
    return [(rv, IOT [(vstypes, aCons qc vstypes)], vs)]

-- Verify the nonfailing type of a function
verifyFuncCall :: Bool -> Expr -> QName -> [Int] -> VerifyStateM ()
verifyFuncCall errorfail exp qf vs
  | qf == pre "failed" || (errorfail && qf == pre "error")
  = addFailedFunc exp Nothing
  | otherwise = do
    atype <- getCallType qf (length vs)
    if isTotalACallType atype
      then return ()
      else do
        incrNonTrivialCall
        currfn <- getCurrentFuncName
        printIfVerb 2 $ "FUNCTION " ++ snd currfn ++ ": VERIFY CALL TO " ++
                        snd qf ++ showArgumentVars vs ++
                        " w.r.t. call type: " ++ prettyFunCallAType atype
        showVarExpTypes
        allvts <- getVarTypes
        printIfVerb 3 $ "Current variable types:\n" ++ showVarTypes allvts
        let svts = simplifyVarTypes allvts
        printIfVerb 3 $ "Simplified variable types:\n" ++ showVarTypes svts
        let vts = map (\v -> (v, getVarType v svts)) vs
        printIfVerb 2 $ "Variable types in this call: " ++ printVATypes vts
        if subtypeOfRequiredCallType (map snd vts) atype
          then printIfVerb 2 "CALL TYPE SATISFIED\n"
          else -- Check whether types of call argument variables can be made
               -- more specific to satisfy the call type. If all these variables
               -- are parameters of the current functions, specialize the
               -- call type of this function and analyze it again.
               do printIfVerb 2 "UNSATISFIED CALL TYPE\n"
                  maybe
                    (addFailedFunc exp Nothing)
                    (\newvts -> do
                       printIfVerb 2 $ "COULD BE SATISFIED BY ENSURING:\n" ++
                                       printVATypes newvts
                       addFailedFunc exp (Just newvts)
                    )
                    (specializeToRequiredType vts atype)
 where
  printVATypes = intercalate ", " . map (\ (v,t) -> show v ++ '/' : showType t)

-- Verify whether missing branches exists and are not reachable.
verifyMissingBranches :: Expr -> Int -> [BranchExpr] -> VerifyStateM ()
verifyMissingBranches _ _ [] = do
  currfn <- getCurrentFuncName
  error $ "Function " ++ snd currfn ++ " contains case with empty branches!"
verifyMissingBranches exp casevar (Branch (Pattern qc _) _ : bs) = do
  allcons <- getAllCons
  let otherqs  = map ((\p -> (patCons p, length(patArgs p))) . branchPattern) bs
      siblings = maybe (error $ "Siblings of " ++ snd qc ++ " not found!")
                       id
                       (getSiblingsOf allcons qc)
      missingcs = siblings \\ otherqs -- constructors having no branches
  currfn <- getCurrentFuncName
  unless (null missingcs) $ do
    incrIncompleteCases
    cvtype <- getVarTypes >>= return . getVarType casevar
    let posscs = map fst
                     (filter (\(c,ar) -> let ctype = aCons c (anyTypes ar)
                                         in joinType cvtype ctype /= emptyType)
                             missingcs)
    unless (null posscs) $ do
      printIfVerb 2 $ showIncompleteBranch currfn exp posscs ++ "\n"
      showVarExpTypes
      addMissingCase exp posscs
verifyMissingBranches exp casevar (Branch (LPattern lit) _ : bs) = do
  incrIncompleteCases
  currfn <- getCurrentFuncName
  let lits = lit : map (patLiteral . branchPattern) bs
  cvtype <- getVarTypes >>= return . getVarType casevar
  unless (isSubtypeOf cvtype (foldr1 lubType (map aLit lits))) $ do
    printIfVerb 2 $ showIncompleteBranch currfn exp [] ++ "\n"
    showVarExpTypes
    addMissingCase exp []

  
-- Verify a branch where the first argument is the case argument variable
-- and the second argument is the variable identifying the case expression.
verifyBranch :: Int -> Int -> BranchExpr
             -> VerifyStateM  [(Int, InOutType, [Int])]
verifyBranch casevar ve (Branch (LPattern l)    e) = do
  vts <- getVarTypes
  let branchvartypes = bindVarInIOTypes casevar (aLit l) vts
  if getVarType casevar branchvartypes == emptyType
    then return [] -- unreachable branch
    else do setVarTypes branchvartypes
            iots <- verifyVarExpr ve e
            setVarTypes vts
            return iots
verifyBranch casevar ve (Branch (Pattern qc vs) e) = do
  addVarExps (map (\v -> (v, Var v)) vs)
  vts <- getVarTypes
  let pattype        = aCons qc (anyTypes (length vs))
      branchvartypes = simplifyVarTypes (bindVarInIOTypes casevar pattype vts)
      casevartype    = getVarType casevar branchvartypes
  if casevartype == emptyType
    then return [] -- unreachable branch
    else do setVarTypes branchvartypes
            mapM_ (\(v,t) -> addVarType (ioVarType v t))
                  (zip vs (argTypesOfCons qc (length vs) casevartype))
            --mapM_ addVarAnyType vs
            iots <- verifyVarExpr ve e
            setVarTypes vts
            return iots

-- Gets the abstract type of a variable w.r.t. a set of variable types.
getVarType :: Int -> [VarType] -> AType
getVarType v viots =
  let vts = filter (\ (rv, _, _) -> rv == v) viots
  in if null vts
       then error $ "Type of variable " ++ show v ++ " not found!"
       else let rts = concatMap (\ (_, IOT iots, _) -> map snd iots) vts 
            in if null rts then emptyType
                           else foldr1 lubType rts

------------------------------------------------------------------------------
--- Computes for a given set of function declarations in a module
--- a mapping from module function names to the list of function
--- declarations where these names are used in the right-hand side.
funcDecls2Usage :: String -> [FuncDecl] -> Map.Map QName [FuncDecl]
funcDecls2Usage mname fdecls = addFDecls (Map.empty) fdecls
 where
  addFDecls m []       = m
  addFDecls m (fd:fds) =
    let rhsfuns = filter (\f -> fst f == mname) (usedFuncsInFunc fd)
    in Map.insertListWith unionFDecls (map (\qf -> (qf,[fd])) rhsfuns)
                          (addFDecls m fds)

unionFDecls :: [FuncDecl] -> [FuncDecl] -> [FuncDecl]
unionFDecls = unionBy (\fd1 fd2 -> funcName fd1 == funcName fd2)

--- Get function names used in the right-hand side of a function declaration.
usedFuncsInFunc :: FuncDecl -> [QName]
usedFuncsInFunc = usedFuncsInRule . funcRule

--- Get function names used in the right-hand side of a rule.
usedFuncsInRule :: Rule -> [QName]
usedFuncsInRule = trRule (\_ body -> usedFuncsInExpr body) (\_ -> [])

--- Get function names used in an expression.
usedFuncsInExpr :: Expr -> [QName]
usedFuncsInExpr e =
  trExpr (const id) (const id) comb lt fr (.) cas branch const e []
 where
  comb ct qn = foldr (.) (combtype ct qn)
  combtype ct qn = case ct of FuncCall       -> (qn:)
                              FuncPartCall _ -> (qn:)
                              _              -> id
  lt bs exp = exp . foldr (.) id (map (\ (_,ns) -> ns) bs)
  fr _ exp = exp
  cas _ exp bs = exp . foldr (.) id bs
  branch _ exp = exp

------------------------------------------------------------------------------
--- A list of any types of a given length.
anyTypes :: Int -> [AType]
anyTypes n = take n (repeat anyType)

------------------------------------------------------------------------------
-- Utilities

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

------------------------------------------------------------------------------
