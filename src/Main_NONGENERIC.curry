-------------------------------------------------------------------------
--- NOTE: This a version of `Main.curry` where the generic `TermDomain`
--- is specialized to type `AType` defined in `Verify.Domain`.
--- This version is used by KiCS2 due to a memory leak with the
--- generic version.
-------------------------------------------------------------------------
--- A tool to verify Curry programs w.r.t. failing computations.
--- Thus, a program successfully verified by this tool should never
--- fail at run-time (apart from explicit error) provided that
--- the call types are satisfied when invoking a function.
---
--- @author Michael Hanus
--- @version December 2023
-------------------------------------------------------------------------

module Main_NONGENERIC (main) where

import Control.Monad              ( unless, when )
import Data.List
import System.Environment         ( getArgs )

import Debug.Trace ( trace )

-- Imports from dependencies:
import Analysis.Types             ( Analysis, analysisName )
--import Analysis.TermDomain
import Control.Monad.Trans.Class  ( lift )
import Control.Monad.Trans.State  ( StateT, get, put, execStateT )
import Data.Char                  ( toLower )
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Set as Set
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
import System.Process             ( exitWith, system )
import Text.Pretty                ( Doc, (<+>), align, pPrint, text )

-- Imports from package modules:
import FlatCurry.Build            ( pre )
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
  bannerText = "Curry Call Pattern Verifier (Version of 13/11/23)"
  bannerLine = take (length bannerText) (repeat '=')

main :: IO ()
main = do
  args <- getArgs
  (opts0,progs) <- processOptions banner args
  -- set analysis to standard analysis if unspecified
  let opts = if null (optDomainID opts0)
               then opts0 { optDomainID = analysisName valueAnalysis }
               else opts0
  if optDomainID opts /= analysisName valueAnalysis
    then do
      let cmd = "curry-calltypes-" ++ map toLower (optDomainID opts)
      putStrLn $ "Different domain, trying executable '" ++ cmd ++ "'..."
      system (cmd ++ concatMap (\a -> " '" ++ a ++ "'") args) >>= exitWith
    else do
      when (optDeleteCache opts) $ deleteVerifyCacheDirectory opts
      case progs of
        [] -> unless (optDeleteCache opts) $ error "Module name missing"
        ms -> runWith valueAnalysis opts ms
 where
  runWith analysis opts ms = do
    astore <- newIORef (AnaStore [])
    mapM_ (runModuleAction (verifyModule analysis astore opts)) ms

-- compatibility definitions for the moment:
type VarTypes = Verify.IOTypes.VarTypes AType
type VarTypesMap = Verify.IOTypes.VarTypesMap AType
type InOutType = Verify.IOTypes.InOutType AType
type ACallType = Verify.CallTypes.ACallType AType


--- Verify a single module.
verifyModule :: Analysis AType -> IORef (AnalysisStore AType) -> Options -> String -> IO ()
verifyModule valueanalysis astore opts mname = do
  printWhenStatus opts $ "Processing module '" ++ mname ++ "':"
  flatprog <- readFlatCurry mname >>= return . transformChoiceInProg
  let fdecls       = progFuncs flatprog
      numfdecls    = length fdecls
      visfuncs     = map funcName (filter ((== Public) . funcVisibility) fdecls)
      numvisfuncs  = length visfuncs
      visfuncset   = Set.fromList visfuncs
      isVisible qf = Set.member qf visfuncset
  imps@(impconss,impacalltypes,_,impiotypes) <-
    if optImports opts
      then do
        whenStatus opts $ putStr $
          "Reading abstract types of imports: " ++ unwords (progImports flatprog)
        readTypesOfModules opts (verifyModule valueanalysis astore)
                           (progImports flatprog)
      else return ([],[],[],[])
  if optTime opts then do whenStatus opts $ putStr "..."
                          (id $## imps) `seq` printWhenStatus opts "done"
                  else printWhenStatus opts ""
  let modcons = allConsOfTypes (progTypes flatprog)
      allcons = modcons ++ impconss
  -- infer initial abstract call types:
  (acalltypes, numntacalltypes, numpubacalltypes) <- id $!!  
    inferCallTypes opts allcons isVisible mname flatprog
  -- infer in/out types:
  (iotypes, numntiotypes, numpubntiotypes) <- id $!!
    inferIOTypes opts valueanalysis astore isVisible flatprog

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
         show numfdecls ++ " functions):"
       pi1 <- getProcessInfos
       (numits,st) <- tryVerifyProg opts 0 vstate mname funusage fdecls
       pi2 <- getProcessInfos
       showVerifyResult opts st mname isVisible
       let tdiff = maybe 0 id (lookup ElapsedTime pi2) -
                   maybe 0 id (lookup ElapsedTime pi1)
       when (optTime opts) $ putStrLn $
         "TOTAL VERIFICATION TIME: " ++ show tdiff ++ " msec"
       return (numits, tdiff, st)
     else return (0, 0, vstate)
  -- print statistics:
  let finalacalltypes   = Map.toList (vstCallTypes vst)
      finalntacalltypes = filter (not . isTotalACallType . snd) finalacalltypes
      (stattxt,statcsv) = showStatistics opts vtime vnumits isVisible
                            numvisfuncs numfdecls
                            (numpubntiotypes, numntiotypes)
                            (numpubacalltypes, numntacalltypes)
                            finalntacalltypes (vstStats vst)
  when (optStats opts) $ putStr stattxt
  when (optVerify opts) $ do
    storeTypes opts mname modcons finalacalltypes [] iotypes
    storeStatistics opts mname stattxt statcsv
  unless (null (optFunction opts)) $ showFunctionInfo opts mname vst

--- Infer the initial (abstract) call types of all functions in a program and
--- return them together with the number of all/public non-trivial call types.
inferCallTypes :: Options -> [[(QName,Int)]] -> (QName -> Bool)
               -> String -> Prog -> IO ([(QName, ACallType)], Int, Int)
inferCallTypes opts allcons isVisible mname flatprog = do
  mtime           <- getModuleModTime mname
  oldpubcalltypes <- readPublicCallTypeModule opts allcons mtime mname
  let fdecls       = progFuncs flatprog
  let calltypes    = unionBy (\x y -> fst x == fst y) oldpubcalltypes
                             (map (callTypeFunc opts allcons) fdecls)
      ntcalltypes  = filter (not . isTotalCallType . snd) calltypes
      pubcalltypes = filter (isVisible . fst) ntcalltypes
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
      pubacalltypes = filter (isVisible . fst) ntacalltypes
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
  return (acalltypes, length ntacalltypes, length pubacalltypes)

--- Infer the in/out types of all functions in a program and return them
--- together with the number of all and public non-trivial in/out types.
inferIOTypes :: Options -> Analysis AType -> IORef (AnalysisStore AType)
             -> (QName -> Bool) -> Prog
             -> IO ([(QName, InOutType)], Int, Int)
inferIOTypes opts valueanalysis astore isVisible flatprog = do
  rvmap <- loadAnalysisWithImports astore valueanalysis opts flatprog
  let iotypes      = map (inOutATypeFunc rvmap) (progFuncs flatprog)
      ntiotypes    = filter (not . isAnyIOType . snd) iotypes
      pubntiotypes = filter (isVisible . fst) ntiotypes
  if optVerb opts > 2
    then putStrLn $ unlines $ "INPUT/OUTPUT TYPES OF ALL OPERATIONS:" :
           showFunResults showIOT iotypes
    else when (optVerb opts > 1 || optIOTypes opts) $
      putStrLn $ unlines $
        ("NON-TRIVIAL INPUT/OUTPUT TYPES OF " ++
         (if optPublic opts then "PUBLIC" else "ALL") ++ " OPERATIONS:") :
        showFunResults showIOT
          (sortFunResults (if optPublic opts then pubntiotypes else ntiotypes))
  return (iotypes, length ntiotypes, length pubntiotypes)

-- Shows the call and in/out type of a given function defined in the module.
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
  let newcts = Map.union (Map.fromList newfailures) (vstCallTypes st)
  let st' = st { vstCallTypes = newcts, vstNewFailed = [] }
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

  printFailures st = whenStatus opts $ do
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

showVerifyResult :: Options -> VerifyState -> String -> (QName -> Bool) -> IO ()
showVerifyResult opts vst mname isvisible = do
  putStr $ "MODULE '" ++ mname ++ "' VERIFIED"
  let calltypes = filter (\ (qf,ct) -> not (isTotalACallType ct) && showFun qf)
                            (Map.toList (vstCallTypes vst))
  if null calltypes
    then putStrLn "\n"
    else putStrLn $ unlines $ " W.R.T. NON-TRIVIAL ABSTRACT CALL TYPES:"
           : showFunResults prettyFunCallAType (sortFunResults calltypes)
 where
  showFun qf = not (optPublic opts) || isvisible qf

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
  , vstVarTypes    :: VarTypesMap       -- map variable to its abstract types
  , vstImpCallTypes:: Map.Map QName ACallType -- call types of imports
  , vstCallTypes   :: Map.Map QName ACallType -- call types of module
  , vstIOTypes     :: Map.Map QName InOutType -- in/out type for all funcs
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

-- Sets the fresh variable index in the state.
setFreshVarIndex :: Int -> VerifyStateM ()
setFreshVarIndex fvi = do
  st <- get
  put $ st { vstFreshVar = fvi }

-- Gets a new fresh variable index.
newFreshVarIndex :: VerifyStateM Int
newFreshVarIndex = do
  v <- fmap vstFreshVar get
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
getVarTypes :: VerifyStateM VarTypesMap
getVarTypes = do
  st <- get
  return $ vstVarTypes st

-- Gets the currently stored types for a given variable.
getVarTypeOf :: Int -> VerifyStateM VarTypes
getVarTypeOf v = do
  st <- get
  return $ maybe [] id (lookup v (vstVarTypes st))

-- Sets all variable types.
setVarTypes :: VarTypesMap -> VerifyStateM ()
setVarTypes vartypes = do
  st <- get
  put $ st { vstVarTypes = vartypes }

-- Adds a new variable type to the current set of variable types.
-- It could be an alternative type for an already existent variable or
-- a type for a new variable.
addVarType :: Int -> VarTypes -> VerifyStateM ()
addVarType v vts = do
  st <- get
  put $ st { vstVarTypes = addVarType2Map v vts (vstVarTypes st) }

-- Adding multiple variable types:
addVarTypes :: VarTypesMap -> VerifyStateM ()
addVarTypes vtsmap = do
  st <- get
  put $ st { vstVarTypes = concVarTypesMap (vstVarTypes st) vtsmap }

-- Adds a new variable `Any` type to the current set of variable types.
addVarAnyType :: Int -> VerifyStateM ()
addVarAnyType v = addVarType v (ioVarType anyType)

-- Removes an `Any` type for a given variable from the current
-- set of variable types.
-- Used to remove the initial `Any` types in let bindings.
removeVarAnyType :: Int -> VerifyStateM ()
removeVarAnyType v = do
  st <- get
  let vtsmap = vstVarTypes st
      vtsmap' = maybe vtsmap
                      (\vts -> setVarTypeInMap v
                                               (filter (not . isAnyIOType) vts)
                                               vtsmap)
                      (lookup v vtsmap)
  put $ st { vstVarTypes = vtsmap' }
 where
  isAnyIOType (vt,vs) =
    case (vt,vs) of (IOT [([], at)], []) -> isAnyType at
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
  return $
    if qf == pre "error" && optError (vstToolOpts st)
      then failACallType
      else maybe (maybe (trace ("Warning: call type of operation " ++
                                show qf ++ " not found!") trivialACallType)
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
  ctype    <- getCallType qf (length vs)
  rhstypes <- mapM (\f -> getCallType f 0) (funcsInExpr exp)
  if all isTotalACallType (ctype:rhstypes)
   then printIfVerb 2 $ "not checked since trivial"
   else maybe (printIfVerb 2 $ "not checked since marked as always failing")
             (\atargs -> do
                setVarTypes (map (\(v,at) -> (v, [(IOT [([], at)], [])]))
                                 (zip vs atargs))
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
                                   else return [(v, ioVarType anyType)]
              addVarTypes iots
              return v
  _     -> do v <- newFreshVarIndex
              addVarExps [(v,exp)]
              iots <- if verifyexp then verifyVarExpr v exp
                                   else return [(v, ioVarType anyType)]
              addVarTypes iots
              return v

-- Verify an expression identified by variable (first argument).
-- The in/out variable types collected for the variable are returned.
verifyVarExpr :: Int -> Expr -> VerifyStateM VarTypesMap
verifyVarExpr ve exp = case exp of
  Var v         -> if v == ve
                     then return []
                     else do
                       --lift $ putStrLn $ "Expression with different vars: " ++
                       --                  show (v,ve)
                       --showVarExpTypes
                       vtypes <- getVarTypeOf v
                       -- TODO: improve by handling equality constraint v==ve
                       -- instead of copying the current types for v to ve:
                       return $ [(ve, vtypes)]
  Lit l         -> return [(ve, [(IOT [([], aLit l)], [])])]
  Comb ct qf es -> checkDivOpNonZero exp $ do
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
                     return [(ve, [(ftype, vs)])]
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
                      addVarTypes (concat iotss)
                      mapM_ (addAnyTypeIfUnknown . fst) bs
                      verifyVarExpr ve e
  Free vs e     -> do addVarExps (map (\v -> (v, Var v)) vs)
                      mapM_ addVarAnyType vs
                      verifyVarExpr ve e
  Or e1 e2      -> do iots1 <- verifyVarExpr ve e1 -- 
                      iots2 <- verifyVarExpr ve e2
                      return (concVarTypesMap iots1 iots2)
  Case _ ce bs  -> do cv <- verifyExpr True ce
                      verifyMissingBranches exp cv bs
                      iotss <- mapM (verifyBranch cv ve) bs
                      return (foldr concVarTypesMap [] iotss)
  Typed e _     -> verifyVarExpr ve e -- TODO: use type info
 where
  -- adds Any type for a variable if it is unknown
  addAnyTypeIfUnknown v = do
    vts <- getVarTypeOf v
    when (null vts) (addVarAnyType v)

  -- Return an input/output type for a constructor and its arguments
  returnConsIOType qc vs rv = do
    vts <- getVarTypes
    let vstypes = map (flip getVarType vts) vs
    --let anys = anyTypes (length vs)  -- TODO: use vs types from VarTypes!!!!
    --return [(rv, IOT [(anys, aCons qc anys)], vs)]
    return [(rv, [(IOT [(vstypes, aCons qc vstypes)], vs)])]

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

-- Auxiliary operation to support specific handling of applying some division
-- operation to non-zero integer constants. If the expression is a call
-- to a `div` or `mod` operation where the second argument is a non-zero
-- constant, return just the first argument, otherwise `Nothing`.
-- This is specific to the current implementation of div/mod where a call
-- like `div e n` is translated into the FlatCurry expression
-- `apply (apply Prelude._impl#div#Prelude.Integral#Prelude.Int e) n`
checkDivOpNonZero :: Expr -> VerifyStateM VarTypesMap -> VerifyStateM VarTypesMap
checkDivOpNonZero exp cont = case exp of
  Comb FuncCall ap1 [ Comb FuncCall ap2 [Comb FuncCall dm _, arg1], nexp]
      | ap1 == apply && ap2 == apply && dm `elem` divops && isNonZero nexp
    -> do verifyExpr True arg1
          return []
  _ -> cont
 where
  isNonZero e = case e of
    Lit (Intc i) -> i /= 0  -- a non-zero literal
    Comb FuncCall ap [ Comb FuncCall fromint _ , nexp] 
      -> ap == apply && fromint == pre "fromInt" && isNonZero nexp -- fromInt ..
    _            -> False

  apply = pre "apply"

  divops =
    map pre [ "_impl#div#Prelude.Integral#Prelude.Int"
            , "_impl#mod#Prelude.Integral#Prelude.Int"
            , "_impl#quot#Prelude.Integral#Prelude.Int"
            , "_impl#rem#Prelude.Integral#Prelude.Int"
            , "div", "mod", "quot", "rem" ]


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
verifyBranch :: Int -> Int -> BranchExpr -> VerifyStateM  VarTypesMap
verifyBranch casevar ve (Branch (LPattern l)    e) = do
  vts <- getVarTypes
  let branchvartypes = bindVarInIOTypes casevar (aLit l) vts
  if isEmptyType (getVarType casevar branchvartypes)
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
  if isEmptyType casevartype
    then return [] -- unreachable branch
    else do setVarTypes branchvartypes
            mapM_ (\(v,t) -> addVarType v (ioVarType t))
                  (zip vs (argTypesOfCons qc (length vs) casevartype))
            --mapM_ addVarAnyType vs
            iots <- verifyVarExpr ve e
            setVarTypes vts
            return iots

-- Gets the abstract type of a variable w.r.t. a set of variable types.
getVarType :: Int -> VarTypesMap -> AType
getVarType v vtsmap =
  maybe (error $ "Type of variable " ++ show v ++ " not found!")
        (\vts -> let rts = concatMap (\ (IOT iots, _) -> map snd iots) vts 
                 in if null rts then emptyType
                                else foldr1 lubType rts)
        (lookup v vtsmap)

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
usedFuncsInRule = trRule (\_ body -> funcsInExpr body) (\_ -> [])

------------------------------------------------------------------------------
--- A list of any types of a given length.
anyTypes :: Int -> [AType]
anyTypes n = take n (repeat anyType)

------------------------------------------------------------------------------
-- Utilities

------------------------------------------------------------------------------
