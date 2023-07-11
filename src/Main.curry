-------------------------------------------------------------------------
--- A tool to verify Curry programs w.r.t. failing computations.
--- Thus, a program successfully verified by this tool should never
--- fail at run-time (apart from explicit error) provided that
--- the call types are satisfied when invoking a function.
---
--- @author Michael Hanus
--- @version July 2023
-------------------------------------------------------------------------

module Main where

import Control.Monad              ( unless, when )
import Data.List
import System.Environment         ( getArgs )

import Debug.Trace ( trace )

-- Imports from dependencies:
import Analysis.ProgInfo
import Analysis.Values
import Analysis.Types
import CASS.Server                ( analyzeGeneric, analyzePublic )
import Control.Monad.Trans.Class  ( lift )
import Control.Monad.Trans.State  ( StateT, get, put, execStateT )
import Data.IORef
import qualified Data.Map as Map
import Debug.Profile
import FlatCurry.Files
import FlatCurry.Goodies
import qualified FlatCurry.Pretty as FCP
import FlatCurry.Types
import System.CurryPath           ( runModuleAction )
import System.Directory           ( createDirectoryIfMissing, doesFileExist )
import System.FilePath            ( (</>) )
import Text.Pretty                ( pPrint )

-- Imports from package modules:
import Verify.CallTypes
import Verify.Files
import Verify.Helpers
import Verify.IOTypes
import Verify.Options

------------------------------------------------------------------------------
banner :: String
banner = unlines [bannerLine, bannerText, bannerLine]
 where
  bannerText = "Curry Call Pattern Verifier (Version of 11/07/23)"
  bannerLine = take (length bannerText) (repeat '=')

main :: IO ()
main = do
  args <- getArgs
  (opts,progs) <- processOptions banner args
  case progs of
    [] -> error "Module name missing"
    ms -> do astore <- newIORef (AnaStore [])
             mapM_ (runModuleAction (verifyModule astore opts)) ms

--- Verify a single module.  
verifyModule :: IORef (AnalysisStore AType) -> Options -> String -> IO ()
verifyModule astore opts mname = do
  printWhenStatus opts $ "Processing module '" ++ mname ++ "':"
  mtime    <- getModuleModTime mname
  flatprog <- readFlatCurry mname >>= return . transformChoiceInProg
  let fdecls   = progFuncs flatprog
      visfuncs = map funcName (filter ((== Public) . funcVisibility) fdecls)
  whenStatus opts $ putStr $
    "Reading abstract types of imports: " ++ unwords (progImports flatprog)
  imps@(impconss,impcalltypes,impiotypes) <-
    if optVerify opts
      then readTypesOfModules opts (verifyModule astore) (progImports flatprog)
      else return ([],[],[])
  if optTime opts then do whenStatus opts $ putStr "..."
                          (id $## imps) `seq` printWhenStatus opts "done"
                  else printWhenStatus opts ""
  let allconsar = allConsOfTypes (progTypes flatprog) ++ impconss
      allcons   = map (map fst) allconsar
  oldpubcalltypes <- readPublicCallTypeModule opts allconsar mtime mname
  mboldcalltypes  <- readCallTypeFile opts mtime mname
  let calltypes    = unionBy (\x y -> fst x == fst y) oldpubcalltypes
                             (maybe (map (callTypeFunc opts allcons) fdecls)
                                    id
                                    mboldcalltypes)
      ntcalltypes  = filter (not . isTotalCallType . snd) calltypes
      pubcalltypes = filter ((`elem` visfuncs) . fst) ntcalltypes
  if optVerb opts > 2
    then do putStrLn $ unlines $ "CALL TYPES OF ALL OPERATIONS:" :
                       showFunResults prettyFunCallTypes calltypes
    else when (optVerb opts > 1 || optCallTypes opts) $
      putStrLn $ unlines $ "NON-TRIVIAL CALL TYPES OF PUBLIC OPERATIONS:" :
        showFunResults prettyFunCallTypes pubcalltypes
  rvinfo <- loadAnalysisWithImports astore resultValueAnalysis opts flatprog
  let iotypes      = map (inOutATypeFunc (cass2AType rvinfo)) fdecls
      ntiotypes    = filter (not . isAnyIOType . snd) iotypes
      pubntiotypes = filter ((`elem` visfuncs) . fst) ntiotypes
  if optVerb opts > 2
    then putStrLn $ unlines $ "INPUT/OUTPUT TYPES OF ALL OPERATIONS:" :
           showFunResults showIOT iotypes
    else when (optVerb opts > 1 || optIOTypes opts) $
      putStrLn $ unlines $
        "NON-TRIVIAL INPUT/OUTPUT TYPES OF PUBLIC OPERATIONS:" :
        showFunResults showIOT pubntiotypes
  let vstate = initVerifyState fdecls allconsar impcalltypes calltypes
                               (iotypes ++ impiotypes) opts
      funusage = funcDecls2Usage mname (progFuncs flatprog)
  printWhenAll opts $ unlines $
    ("Function usage in module '" ++ mname ++ "':") :
    map (\ (qf, qfs) -> snd qf ++ ": used in " ++
                        unwords (map (snd . funcName) qfs))
        (Map.toList funusage)
  vst <-
   if optVerify opts
     then do
       printWhenStatus opts $ "Start verification of '" ++ mname ++ "' (" ++
         show (length fdecls) ++ " functions):"
       pi1 <- getProcessInfos
       st <- tryVerifyProg opts vstate mname funusage fdecls
       pi2 <- getProcessInfos
       let tdiff = maybe 0 id (lookup ElapsedTime pi2) -
                   maybe 0 id (lookup ElapsedTime pi1)
       when (optTime opts) $ putStrLn $
         "TOTAL VERIFICATION TIME: " ++ show tdiff ++ " msec"
       return st
     else return vstate
  -- print statistics:
  let stats = showStatistics (optVerify opts) (length fdecls) (length visfuncs)
                             (length pubcalltypes) (length ntcalltypes)
                             (length pubntiotypes) (length ntiotypes) (vstStats vst)
  when (optStats opts) $ putStr stats
  let newcalltypes    = vstCallTypes vst
      newpubcalltypes = filter (\ (qf,ct) -> qf `elem` visfuncs &&
                                             not (isTotalCallType ct)) newcalltypes
  when (optVerify opts) $ do
    storeTypes opts mname (allConsOfTypes (progTypes flatprog))
               newpubcalltypes newcalltypes iotypes
    storeStatistics mname stats

-- Try to verify a module (possible in several iterations).
tryVerifyProg :: Options -> VerifyState -> String -> Map.Map QName [FuncDecl]
              -> [FuncDecl] -> IO VerifyState
tryVerifyProg opts vstate mname funusage fdecls = do
  st <- execStateT (mapM_ verifyFunc fdecls) vstate
  let newfailures = vstNewFailed st
  if null (vstFailedFuncs st) && null (vstPartialBranches st)
    then do
      putStr $ "MODULE '" ++ mname ++ "' VERIFIED"
      let pubcalltypes = filter (\ (qf,ct) -> qf `elem` visfuncs &&
                                              not (isTotalCallType ct))
                                (vstCallTypes st)
      if null pubcalltypes
        then putStrLn "!"
        else putStrLn $ unlines $ " W.R.T. NON-TRIVIAL PUBLIC CALL TYPES:"
               : showFunResults prettyFunCallTypes (sortFunResults pubcalltypes)
    else unless (null newfailures || optVerb opts < 2) $ printFailures st
  unless (null newfailures) $ printWhenStatus opts $ unlines $
    "Operations with refined call types (used in future analyses):" :
    showFunResults prettyFunCallTypes (reverse newfailures)
  let st' = st { vstCallTypes = unionBy (\x y -> fst x == fst y) newfailures
                                        (vstCallTypes st)
               , vstNewFailed = [] }
  if null newfailures
    then do printFailures st'
            return st'
    else do
      let -- functions with refined call types:
          rfuns = map fst (filter (not . isFailCallType . snd) newfailures)
          newfdecls =
            foldr unionFDecls
              (filter (\fd -> funcName fd `elem` rfuns) (vstFuncDecls st))
              (map (\ (qf,_) -> maybe [] id (Map.lookup qf funusage))
                   newfailures)
      printWhenStatus opts $ "Repeat verification with new call types..." ++
        "(" ++ show (length newfdecls) ++ " functions)"
      tryVerifyProg opts st' mname funusage newfdecls
 where
  visfuncs = map funcName (filter ((== Public) . funcVisibility) fdecls)

  printFailures st = do
    unless (null (vstFailedFuncs st)) $
      putStrLn $ "PROGRAM CONTAINS POSSIBLY FAILING FUNCTION CALLS:\n" ++
         unlines (map (\ (qf,_,e) -> "Function '" ++ snd qf ++
                                     "': call '" ++ showExp e ++ "'")
                      (reverse (vstFailedFuncs st)))
    unless (null (vstPartialBranches st)) $
      putStrLn $ "PROGRAM CONTAINS POSSIBLY FAILING FUNCTIONS:\n" ++
         unlines
           (map (\ (qf,_,e,cs) -> showIncompleteBranch qf e cs)
                (reverse (vstPartialBranches st)))

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
-- Store for the analysis information of CASS. Used to avoid multiple reads.
data AnalysisStore a = AnaStore [(String, ProgInfo a)]

-- Loads CASS analysis results for a module and its imported entities.
loadAnalysisWithImports :: (Read a, Show a) =>
   IORef (AnalysisStore a) -> Analysis a -> Options -> Prog -> IO (ProgInfo a)
loadAnalysisWithImports anastore analysis opts prog = do
  maininfo <- getOrAnalyze (progName prog)
  impinfos <- mapM getOrAnalyze (progImports prog)
  return $ foldr combineProgInfo maininfo (map publicProgInfo impinfos)
 where
  getOrAnalyze mname = do
    AnaStore minfos <- readIORef anastore
    maybe (do printWhenStatus opts $ "Getting " ++ analysisName analysis ++
                " for '" ++ mname ++ "' via CASS..."
              minfo <- fmap (either id error) $ analyzeGeneric analysis mname
              writeIORef anastore (AnaStore ((mname,minfo) : minfos))
              return minfo)
          return
          (lookup mname minfos)

-- Transform the result value information from CASS into a mapping w.r.t.
-- into local `AType` values.
cass2AType :: ProgInfo AType -> (QName -> AType)
cass2AType resvalinfo qf =
  maybe (error $ "Result values information of " ++ snd qf ++ " not found!")
        id
        (lookupProgInfo qf resvalinfo)

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
  , vstVarTypes    :: [(Int,InOutType,[Int])] -- relate variable to types
  , vstImpCallTypes:: [(QName,[[CallType]])] -- call types of imports
  , vstCallTypes   :: [(QName,[[CallType]])] -- call types of module
  , vstFuncTypes   :: [(QName,InOutType)]   -- the in/out type for each function
  , vstFailedFuncs :: [(QName,Int,Expr)]     -- functions with illegal calls
  , vstPartialBranches :: [(QName,Int,Expr,[QName])] -- incomplete branches
  , vstNewFailed   :: [(QName,[[CallType]])] -- new failed function call types
  , vstStats    :: (Int,Int) -- statistics: non-trivial calls / incomplete cases
  , vstToolOpts :: Options
  }

showVarTypes :: [(Int, InOutType, [Int])] -> String
showVarTypes = unlines . map showVarType

showVarType :: (Int, InOutType, [Int]) -> String
showVarType (rv, iot, argvs) =
  show rv ++ ": " ++ showIOT iot ++ " " ++ show argvs

initVerifyState :: [FuncDecl] -> [[(QName,Int)]] -> [(QName,[[CallType]])]
                -> [(QName,[[CallType]])] -> [(QName,InOutType)] -> Options
                -> VerifyState
initVerifyState fdecls allcons impcalltypes calltypes ftypes opts =
  VerifyState fdecls (("",""),0,[]) allcons 0 [] [] impcalltypes calltypes
              ftypes [] [] [] (0,0) opts

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

-- Adds a failed function call (represented by the FlatCurry expression)
-- to the current function. If the second argument is `Just vts`, then
-- this call is not failed provided that it can be ensured that the
-- variable types `vts` hold. This information is used to refine the
-- call type of the current function, if possible.
addFailedFunc :: Expr -> Maybe [(Int,AType)] -> VerifyStateM ()
addFailedFunc exp mbvts = do
  st <- get
  let (qf,ar,args) = vstCurrFunc st
      stfail = st { vstFailedFuncs = union [(qf,ar,exp)] (vstFailedFuncs st)
                  , vstNewFailed = union [(qf,failCallType)] (vstNewFailed st) }
  maybe (put stfail)
        (\vts ->
           if all ((`elem` args) . fst) vts
             then do oldct <- getCallType qf ar
                     allcons <- getAllCons
                     let ncts = map (\v -> aType2CallType allcons
                                             (maybe anyType id (lookup v vts)))
                                    args
                         newct = map (\cts -> map (uncurry joinCT)
                                                  (zip cts ncts)) oldct
                     printIfVerb 2 $ "TRY TO REFINE FUNCTION CALL TYPE TO: " ++
                                     prettyFunCallTypes newct
                     put $ stfail { vstNewFailed = union [(qf,newct)]
                                                         (vstNewFailed st) }
             else do printIfVerb 2 "CANNOT REFINE FUNCTION CALL TYPE"
                     put stfail
        )
        mbvts

-- Adds an info about cases with missing branches in the current function.
addMissingCase :: Expr -> [QName] -> VerifyStateM ()
addMissingCase exp qcs = do
  st <- get
  let (qf,ar,_) = vstCurrFunc st
  put $
    st { vstPartialBranches = union [(qf,ar,exp,qcs)] (vstPartialBranches st)
       , vstNewFailed = union [(qf,[])] (vstNewFailed st) }

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

-- Set the expressions for variables.
getVarTypes :: VerifyStateM [(Int,InOutType,[Int])]
getVarTypes = do
  st <- get
  return $ vstVarTypes st

-- Set the expressions for variables.
setVarTypes :: [(Int,InOutType,[Int])] -> VerifyStateM ()
setVarTypes vartypes = do
  st <- get
  put $ st { vstVarTypes = vartypes }

-- Adds new variable types.
addVarType :: (Int,InOutType,[Int]) -> VerifyStateM ()
addVarType vartype = do
  st <- get
  --lift $ putStrLn $ "addVarType: " ++ showVarType vartype
  put $ st { vstVarTypes = vstVarTypes st ++ [vartype] }

-- Gets the call type for a given operation.
getCallType :: QName -> Int -> VerifyStateM [[CallType]]
getCallType qf ar = do
  st <- get
  return $ maybe
    (maybe (trace ("Warning: call type of operation " ++ show qf ++
                   " not found!") [take ar (repeat AnyT)])
           id
           (lookup qf (vstImpCallTypes st)))
    id
    (lookup qf (vstCallTypes st))

-- Gets the in/out type for an operation of a given arity.
-- If the operation is not found, returns a general type.
getFuncType :: QName -> Int -> VerifyStateM InOutType
getFuncType qf ar = do
  st <- get
  maybe (do lift $ putStrLn $ "WARNING: in/out type of " ++ show qf ++
                              " not found!"
            return $ IOT [(take ar (repeat anyType), anyType)])
        return
        (lookup qf (vstFuncTypes st))

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
  Rule vs exp -> do setCurrentFunc qf ar vs
                    verifyFuncRule vs exp
  External _  -> return ()

verifyFuncRule :: [Int] -> Expr -> VerifyStateM ()
verifyFuncRule vs exp = do
  setFreshVarIndex (maximum (0 : vs ++ allVars exp) + 1)
  setVarExps  (map (\v -> (v, Var v)) vs)
  qf <- getCurrentFuncName
  printIfVerb 2 $ "CHECKING FUNCTION " ++ snd qf
  ctype <- getCallType qf (length vs)
  if isFailCallType ctype
    then printIfVerb 2 $ "not checked since marked as always failing"
    else do
      let ctargs = map (\cts -> if null cts then AnyT else foldr1 unionCT cts)
                       (transpose ctype)
          atargs = map callType2AType ctargs
      setVarTypes (map (\ (v,at) -> (v, IOT [([],at)], [])) (zip vs atargs))
      showVarExpTypes
      verifyExpr exp
      return ()
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
      unlines (map (\ (v,e) -> show v ++ " |-> " ++ showExp e)
                         (vstVarExp st))
    lift $ putStr $ "Variable types\n" ++ showVarTypes (vstVarTypes st)

showExp :: Expr -> String
showExp e =
  pPrint (FCP.ppExp FCP.defaultOptions { FCP.qualMode = FCP.QualNone} e)

-- Verify an expression and return the variable used to identify it.
verifyExpr :: Expr -> VerifyStateM Int
verifyExpr exp = case exp of
  Var v -> do iots <- verifyVarExpr v exp
              mapM addVarType iots
              return v
  _     -> do v <- newFreshVarIndex
              addVarExps [(v,exp)]
              iots <- verifyVarExpr v exp
              mapM addVarType iots
              return v

-- Current problem: variable ve is bound to the result of exp,
-- but this is not correct for or/cases!
-- Solution? return result of exp?

-- Verify an expression identified by variable (first argument)
verifyVarExpr :: Int -> Expr -> VerifyStateM [(Int, InOutType, [Int])]
verifyVarExpr ve exp = case exp of
  Var _         -> return []
  Lit l         -> return [(ve, IOT [([], aCons (lit2cons l))], [])]
  Comb ct qf es -> do
    vs <- mapM verifyExpr es
    case ct of
      FuncCall -> do opts <- getToolOptions
                     verifyFuncCall (optError opts) exp qf vs
                     ftype <- getFuncType qf (length es)
                     return [(ve, ftype, vs)]
      FuncPartCall n -> -- note: also partial calls are considered as constr.
                  do ctype <- getCallType qf (n + length es)
                     unless (isTotalCallType ctype) $ do
                       printIfVerb 2 $ "UNSATISFIED CALL TYPE: " ++
                         "partial application of non-total function\n"
                       addFailedFunc exp Nothing
                     return [consIOType qf vs ve]
      _        -> -- note: also partial calls are considered as constr.
                  do return [consIOType qf vs ve]
  Let bs e      -> do addVarExps bs
                      iotss <- mapM (\ (v,be) -> verifyVarExpr v be) bs
                      mapM addVarType (concat iotss)
                      verifyVarExpr ve e
  Free vs e     -> do addVarExps (map (\v -> (v, Var v)) vs)
                      verifyVarExpr ve e
  Or e1 e2      -> do iots1 <- verifyVarExpr ve e1 -- 
                      iots2 <- verifyVarExpr ve e2
                      return (iots1 ++ iots2)
  Case _ ce bs  -> do cv <- verifyExpr ce
                      verifyMissingBranches exp cv bs
                      iotss <- mapM (verifyBranch cv ve) bs
                      return (concat iotss)
  Typed e _     -> verifyVarExpr ve e -- TODO: use type info
 where
  -- create input/output type for a constructor (improve by type info?)
  consIOType qc vs rv =
    (rv, IOT [(take (length vs) (repeat anyType), aCons qc)], vs)

-- Verify the nonfailing type of a function
verifyFuncCall :: Bool -> Expr -> QName -> [Int] -> VerifyStateM ()
verifyFuncCall errorfail exp qf vs
  | qf == pre "failed" || (errorfail && qf == pre "error")
  = addFailedFunc exp Nothing
  | otherwise = do
    ctype <- getCallType qf (length vs)
    if isTotalCallType ctype
      then return ()
      else do
        incrNonTrivialCall
        currfn <- getCurrentFuncName
        printIfVerb 2 $ "FUNCTION " ++ snd currfn ++ ": VERIFY CALL TO " ++
                        snd qf ++ " " ++ show vs ++
                        " w.r.t. call type: " ++ prettyFunCallTypes ctype
        showVarExpTypes
        allvts <- getVarTypes
        printIfVerb 3 $ "Current variable types:\n" ++ showVarTypes allvts
        let svts = simplifyVarTypes allvts
        printIfVerb 3 $ "Simplified variable types:\n" ++ showVarTypes svts
        let vts = map (\v -> (v, getVarType v svts)) vs
        printIfVerb 2 $ "Variable types in this call: " ++ printVATypes vts
        if subtypeOfSomeAT (map snd vts) ctype
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
                    (makeSubtypeOfSomeAT vts ctype)
 where
  printVATypes = intercalate ", " . map (\ (v,t) -> show v ++ '/' : showAType t)

-- Verify whether missing branches exists and are not reachable.
verifyMissingBranches :: Expr -> Int -> [BranchExpr] -> VerifyStateM ()
verifyMissingBranches _ _ [] = do
  currfn <- getCurrentFuncName
  error $ "Function " ++ snd currfn ++ " contains case with empty branches!"
verifyMissingBranches exp casevar (Branch (Pattern qc _) _ : bs) = do
  allcons <- getAllCons >>= return . map (map fst)
  let otherqs   = map (patCons . branchPattern) bs
      siblings = maybe (error $ "Siblings of " ++ snd qc ++ " not found!")
                       id
                       (getSiblingsOf allcons qc)
      missingcs = siblings \\ otherqs -- constructors having no branches
  currfn <- getCurrentFuncName
  unless (null missingcs) $ do
    incrIncompleteCases
    cvtype <- getVarTypes >>= return . getVarType casevar
    let posscs = filter (\c -> joinAType cvtype (aCons c) /= emptyType)
                        missingcs
    unless (null posscs) $ do
      printIfVerb 2 $ showIncompleteBranch currfn exp posscs ++ "\n"
      showVarExpTypes
      addMissingCase exp posscs
verifyMissingBranches exp casevar (Branch (LPattern lit) _ : bs) = do
  incrIncompleteCases
  currfn <- getCurrentFuncName
  let lits = lit : map (patLiteral . branchPattern) bs
  cvtype <- getVarTypes >>= return . getVarType casevar
  unless (subtypeAT cvtype (MCons (map (\l -> (lit2cons l,[])) lits))) $ do
    printIfVerb 2 $ showIncompleteBranch currfn exp [] ++ "\n"
    showVarExpTypes
    addMissingCase exp []

  
-- Verify a branch where the first argument is the case argument variable
-- and the second argument is the variable identifying the case expression.
verifyBranch :: Int -> Int -> BranchExpr
             -> VerifyStateM  [(Int, InOutType, [Int])]
verifyBranch casevar ve (Branch (LPattern l)    e) = do
  vts <- getVarTypes
  let branchvartypes = bindVarInIOTypes casevar (lit2cons l) vts
  if getVarType casevar branchvartypes == emptyType
    then return [] -- unreachable branch
    else do setVarTypes branchvartypes
            iots <- verifyVarExpr ve e
            setVarTypes vts
            return iots
verifyBranch casevar ve (Branch (Pattern qc vs) e) = do
  addVarExps (map (\v -> (v, Var v)) vs)
  vts <- getVarTypes
  let branchvartypes = simplifyVarTypes (bindVarInIOTypes casevar qc vts)
  if getVarType casevar branchvartypes == emptyType
    then return [] -- unreachable branch
    else do setVarTypes branchvartypes
            mapM_ (\v -> addVarType (v, IOT [([], anyType)], [])) vs
            iots <- verifyVarExpr ve e
            setVarTypes vts
            return iots

-- Gets the abstract type of a variable w.r.t. a set of variable types.
getVarType :: Int -> [(Int, InOutType, [Int])] -> AType
getVarType v viots =
  let rts = map (\ (rv, IOT iots, _) -> if rv == v then map snd iots
                                                   else [])
                     viots
  in if null rts
       then error $ "Type of variable " ++ show v ++ " not found!"
       else if null (concat rts)
              then emptyType
              else foldr1 lubAType (concat rts)

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
