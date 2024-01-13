-------------------------------------------------------------------------
--- The options of the verification tool together with some
--- related operations.
---
--- @author Michael Hanus
--- @version December 2023
-------------------------------------------------------------------------

module Verify.Options
  ( Options(..), defaultOptions, processOptions
  , whenStatus, printWhenStatus, printWhenIntermediate, printWhenDetails
  , printWhenAll
  )
 where

import Curry.Compiler.Distribution ( curryCompiler, curryCompilerMajorVersion
                                   , curryCompilerMinorVersion
                                   , curryCompilerRevisionVersion )

import Control.Monad         ( when, unless )
import Data.Char             ( toUpper )
import Data.List             ( intercalate )
import Numeric               ( readNat )
import System.Console.GetOpt

import System.CurryPath      ( stripCurrySuffix )
import System.IO             ( hFlush, stdout )
import System.Process        ( exitWith )

data Options = Options
  { optVerb        :: Int  -- verbosity (0: quiet, 1: status, 2: intermediate,
                           --            3: verify details, 4: all)
  , optHelp        :: Bool -- if help info should be printed
  , optFunction    :: String -- show the result for this function
  , optImports     :: Bool -- read/analyze imports/prelude? (only for testing)
  , optDeleteCache :: Bool -- delete the analysis cache?
  , optRerun       :: Bool -- rerun verification of current module
  , optPublic      :: Bool -- show types (call, in/out) of public ops only? 
  , optCallTypes   :: Bool -- show call types
  , optIOTypes     :: Bool -- show input/output types
  , optVerify      :: Bool -- verify call types
  , optSMT         :: Bool -- use SMT solver (Z3) to verify non-fail conditions?
  , optStoreSMT    :: Bool -- store generated SMT scripts (for debugging)
  , optError       :: Bool -- consider Prelude.error as failing operation?
  , optSpecModule  :: Bool -- generate a `..._SPEC` module?
  , optStats       :: Bool -- show and store statitics?
  , optTime        :: Bool -- show elapsed verification time?
  , optDomainID    :: String -- the unique id for the abstract term domain
  }

--- The default options of the verification tool.
defaultOptions :: Options
defaultOptions =
  Options 1 False "" True False False True False False True True False False
          False False False ""

--- Process the actual command line argument and return the options
--- and the name of the main program.
processOptions :: String -> [String] -> IO (Options,[String])
processOptions banner argv = do
  let (funopts, args, opterrors) = getOpt Permute options argv
      opts = foldl (flip id) defaultOptions funopts
  unless (null opterrors)
         (putStr (unlines opterrors) >> printUsage >> exitWith 1)
  when (optHelp opts) (printUsage >> exitWith 0)
  return (opts, map stripCurrySuffix args)
 where
  printUsage = putStrLn (banner ++ "\n" ++ usageText)

-- Help text
usageText :: String
usageText =
  usageInfo ("Usage: curry-calltypes [options] <module names>\n") options

-- Definition of actual command line options.
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]
           (NoArg (\opts -> opts { optHelp = True }))
           "print help and exit"
  , Option "q" ["quiet"]
           (NoArg (\opts -> opts { optVerb = 0 }))
           "run quietly (no output, only exit code)"
  , Option "v" ["verbosity"]
            (OptArg (maybe (checkVerb 2) (safeReadNat checkVerb)) "<n>")
            "verbosity level:\n0: quiet (same as `-q')\n1: show status messages (default)\n2: show intermediate results (same as `-v')\n3: show also verification details\n4: show all details"
  , Option "a" ["all"]
            (NoArg (\opts -> opts { optPublic = False }))
           "show types for all (also private) operations"
  , Option "c" ["calltypes"]
            (NoArg (\opts -> opts { optCallTypes = True }))
           "show call types"
  , Option "d" ["domain"]
           (ReqArg checkDomain "<d>")
           "the analysis domain (Values|Values2|Values5)"
  , Option "" ["delete"]
           (NoArg (\opts -> opts { optDeleteCache = True }))
           ("delete all cache files (for " ++ sysname ++ ")")
  , Option "e" ["error"]
           (NoArg (\opts -> opts { optError = True }))
           "consider 'Prelude.error' as a failing operation"
  , Option "f" ["function"]
            (ReqArg (\s opts -> opts { optFunction = s }) "<f>")
            "show the call and in/out type for function <f>"
  , Option "i" ["iotypes"]
            (NoArg (\opts -> opts { optIOTypes = True }))
           "show input/output types"
  , Option "" ["noimports"]
           (NoArg (\opts -> opts { optImports = False }))
           "do not read/analyze imported modules (for testing)"
  , Option "" ["nosmt"]
           (NoArg (\opts -> opts { optSMT = False }))
           "do not use SMT solver (Z3) to verify non-fail\nconditions"
  , Option "n" ["noverify"]
           (NoArg (\opts -> opts { optVerify = False }))
           "do not verify call types in function calls"
  , Option "r" ["rerun"]
           (NoArg (\opts -> opts { optRerun = True }))
           "rerun verification of current module\n(ignore results of previous verification)"
  , Option "s" ["statistics"]
           (NoArg (\opts -> opts { optStats = True }))
           "show/store statistics (functions, failures,...)"
  , Option "" ["storesmt"]
           (NoArg (\opts -> opts { optStoreSMT = True }))
           "store generated SMT scripts (for debugging)"
  , Option "" ["storespec"]
           (NoArg (\opts -> opts { optSpecModule = True }))
           "store call types/conditions in '..._SPEC' module"
  , Option "t" ["time"]
           (NoArg (\opts -> opts { optTime = True }))
           "show total verification time for each module"
  ]
 where
  safeReadNat opttrans s opts = case readNat s of
    [(n,"")] -> opttrans n opts
    _        -> error "Illegal number argument (try `-h' for help)"

  checkVerb n opts = if n >= 0 && n <= 4
                       then opts { optVerb = n }
                       else error "Illegal verbosity level (try `-h' for help)"

  checkDomain s opts =
    if s `elem` ["Values", "Values2", "Values5"]
      then opts { optDomainID = s }
      else error "Illegal domain ID, allowed values: Value|Values2|Values5"

  sysname = curryCompiler ++ "-" ++
            intercalate "."
              (map show [ curryCompilerMajorVersion
                        , curryCompilerMinorVersion
                        , curryCompilerRevisionVersion ])

-------------------------------------------------------------------------

whenStatus :: Options -> IO () -> IO ()
whenStatus opts = when (optVerb opts > 0)

printWhenStatus :: Options -> String -> IO ()
printWhenStatus opts s = whenStatus opts (printWT s)

printWhenIntermediate :: Options -> String -> IO ()
printWhenIntermediate opts s =
  when (optVerb opts > 1) (printWT s)

printWhenDetails :: Options -> String -> IO ()
printWhenDetails opts s =
 when (optVerb opts > 2) (printWT s)

printWhenAll :: Options -> String -> IO ()
printWhenAll opts s =
 when (optVerb opts > 3) (printWT s)

printWT :: String -> IO ()
printWT s = do putStrLn $ s --"NON-FAIL INFERENCE: " ++ s
               hFlush stdout

---------------------------------------------------------------------------
