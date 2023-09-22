-------------------------------------------------------------------------
--- The options of the verification tool together with some
--- related operations.
---
--- @author Michael Hanus
--- @version July 2023
-------------------------------------------------------------------------

module Verify.Options
  ( Options(..), defaultOptions, processOptions
  , whenStatus, printWhenStatus, printWhenIntermediate, printWhenAll
  )
 where

import Control.Monad         ( when, unless )
import Data.Char             ( toUpper )
import System.Console.GetOpt
import Numeric               ( readNat )
import System.Process        ( exitWith )

import System.CurryPath      ( stripCurrySuffix )

data Options = Options
  { optVerb      :: Int   -- verbosity (0: quiet, 1: status, 2: interm, 3: all)
  , optHelp      :: Bool  -- if help info should be printed
  , optRerun     :: Bool  -- rerun verification of current module
  , optPublic    :: Bool  -- show types (call, in/out) of public ops only? 
  , optCallTypes :: Bool  -- show call types
  , optIOTypes   :: Bool  -- show input/output types
  , optVerify    :: Bool  -- verify call types
  , optError     :: Bool  -- consider Prelude.error as failing operation?
  , optStats     :: Bool  -- show statitics?
  , optTime      :: Bool  -- show elapsed verification time?
  , optWrite     :: Bool  -- write a `CALLTYPES` module for later use?
  }

--- The default options of the verification tool.
defaultOptions :: Options
defaultOptions =
  Options 1 False False True False False True False False False False

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
            "verbosity level:\n0: quiet (same as `-q')\n1: show status messages (default)\n2: show intermediate results (same as `-v')\n3: show all details"
  , Option "a" ["all"]
            (NoArg (\opts -> opts { optPublic = False }))
           "show types for all (also private) operations"
  , Option "c" ["calltypes"]
            (NoArg (\opts -> opts { optCallTypes = True }))
           "show call types"
  , Option "i" ["iotypes"]
            (NoArg (\opts -> opts { optIOTypes = True }))
           "show input/output types"
  , Option "e" ["error"]
           (NoArg (\opts -> opts { optError = True }))
           "consider 'Prelude.error' as a failing operation"
  , Option "n" ["noverify"]
           (NoArg (\opts -> opts { optVerify = False }))
           "do not verify call types in function calls"
  , Option "r" ["rerun"]
           (NoArg (\opts -> opts { optRerun = True }))
           "rerun verification of current module\n(ignore results of previous verification)"
  , Option "s" ["statistics"]
           (NoArg (\opts -> opts { optStats = True }))
           "show statistics (functions, failures,...)"
  , Option "t" ["time"]
           (NoArg (\opts -> opts { optTime = True }))
           "show total verification time for each module"
  , Option "w" ["write"]
           (NoArg (\opts -> opts { optWrite = True }))
           "write  a '..._CALLTYPES' module with required\ncall types"
  ]
 where
  safeReadNat opttrans s opts = case readNat s of
    [(n,"")] -> opttrans n opts
    _        -> error "Illegal number argument (try `-h' for help)"

  checkVerb n opts = if n>=0 && n<4
                       then opts { optVerb = n }
                       else error "Illegal verbosity level (try `-h' for help)"

-------------------------------------------------------------------------

whenStatus :: Options -> IO () -> IO ()
whenStatus opts = when (optVerb opts > 0)

printWhenStatus :: Options -> String -> IO ()
printWhenStatus opts s = whenStatus opts (printWT s)

printWhenIntermediate :: Options -> String -> IO ()
printWhenIntermediate opts s =
  when (optVerb opts > 1) (printWT s)

printWhenAll :: Options -> String -> IO ()
printWhenAll opts s =
 when (optVerb opts > 2) (printWT s)

printWT :: String -> IO ()
printWT s = putStrLn $ s --"NON-FAILING ANALYSIS: " ++ s

---------------------------------------------------------------------------
