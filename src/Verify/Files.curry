------------------------------------------------------------------------------
--- Operations to write and read auxiliary files containing
--- verification information.
---
--- @author Michael Hanus
--- @version July 2023
-----------------------------------------------------------------------------

module Verify.Files
   ( readTypesOfModules, readPublicCallTypeModule, readCallTypeFile
   , showStatistics, storeStatistics, storeTypes
   )
  where

import Control.Monad        ( unless, when )
import Data.List            ( isPrefixOf, isSuffixOf, sortBy )

import AbstractCurry.Build
import AbstractCurry.Files  ( readCurry )
import AbstractCurry.Pretty ( showCProg )
import AbstractCurry.Select
import AbstractCurry.Types hiding ( pre )
import Contract.Names       ( decodeContractName, encodeContractName )
import Data.Time            ( ClockTime, compareClockTime )
import System.CurryPath     ( currySubdir, lookupModuleSourceInLoadPath
                            , modNameToPath )
import System.Directory
import System.FilePath      ( (</>), dropFileName, joinPath, splitDirectories )
import System.IOExts        ( readCompleteFile )

import PackageConfig        ( getPackagePath )
import Verify.CallTypes
import Verify.Helpers
import Verify.IOTypes
import Verify.Options

------------------------------------------------------------------------------
-- Definition of directory and file names for various data.

-- The name of the file containing statistical information about the
-- verification of a module.
statsFile :: String -> String
statsFile mname = verifyDataDir </> mname ++ "-STATISTICS"

--- The name of the directory containing all data generated and used by
--- this tool.
callTypesDataDir :: String
callTypesDataDir = "CALLTYPES"

--- The name of the directory containing the computed infos for modules.
verifyDataDir :: String
verifyDataDir = callTypesDataDir </> "verifydata" </>
                joinPath (tail (splitDirectories currySubdir))

-- The name of the file containing all call types of a module.
callTypesFile :: String -> String
callTypesFile mname = verifyDataDir </> mname ++ "-CALLTYPES"

-- The name of the file containing all input/output types of a module.
ioTypesFile :: String -> String
ioTypesFile mname = verifyDataDir </> mname ++ "-IOTYPES"

-- The name of the file containing all constructor of a module.
consTypesFile :: String -> String
consTypesFile mname = verifyDataDir </> mname ++ "-CONSTYPES"

-- The name of the Curry module where the call type specifications are stored.
callTypesModule :: String -> String
callTypesModule mname = mname ++ "_CALLTYPES"

------------------------------------------------------------------------------
-- Show statistics:
showStatistics :: Bool -> Int -> Int -> Int -> Int -> Int
               -> Int -> (Int,Int) -> String
showStatistics withverify numallfuncs numvisfuncs numpubcalltypes
               numallcalltypes numpubiotypes numalliotypes
               (numcalls, numcases) = unlines $
  [ "Functions                      (public / all): " ++
    show numvisfuncs ++ " / " ++ show numallfuncs
  , "Non-trivial call types         (public / all): " ++
     show numpubcalltypes ++ " / " ++ show numallcalltypes
  , "Non-trivial input/output types (public / all): " ++
     show numpubiotypes ++ " / " ++ show numalliotypes ] ++
   (if withverify
      then [ "Non-trivial function calls checked           : " ++
              show numcalls
           , "Incomplete case expressions checked          : " ++
              show numcases ]
      else [])

--- Store the statitics for a module in a file.
storeStatistics :: String -> String -> IO ()
storeStatistics mname = writeFile (statsFile mname)

------------------------------------------------------------------------------
-- Stores non-trivial call types and non-trivial input/output types.
storeTypes :: Options -> String -> [[(QName,Int)]]
           -> [(QName,[[CallType]])] -- public non-trivial call types
           -> [(QName,[[CallType]])] -- all call types
           -> [(QName,InOutType)]    -- all input output types
           -> IO ()
storeTypes opts mname allcons pubntcalltypes calltypes iotypes = do
  createDirectoryIfMissing True verifyDataDir
  writeFile (consTypesFile mname) (show allcons)
  writeFile (callTypesFile mname)
    (unlines (map (\ ((_,fn),ct) -> show (fn,ct)) (filterMod calltypes)))
  writeFile (ioTypesFile mname)
    (unlines (map (\ ((_,fn), IOT iots) -> show (fn,iots)) (filterMod iotypes)))
  writeCallTypeSpecMod opts mname (sortFunResults pubntcalltypes)
 where
  filterMod xs = filter (\ ((mn,_),_) -> mn == mname) xs

-- Try to read constructors, non-trivial call types, and
-- non-trivial input/output types for a given module.
-- If the data files do not exist or are older than the source of the
-- module, `Nothing` is returned.
tryReadTypes :: Options -> String
  -> IO (Maybe ([[(QName,Int)]], [(QName,[[CallType]])], [(QName,InOutType)]))
tryReadTypes opts mname = do
  let csfile = consTypesFile mname
      ctfile = callTypesFile mname
      iofile = ioTypesFile   mname
  csexists <- doesFileExist csfile
  ctexists <- doesFileExist ctfile
  ioexists <- doesFileExist iofile
  if not (csexists && ctexists && ioexists)
    then return Nothing
    else do
      srctime <- getModuleModTime mname
      cstime  <- getModificationTime csfile
      cttime  <- getModificationTime ctfile
      iotime  <- getModificationTime iofile
      if compareClockTime cstime srctime == GT &&
         compareClockTime cttime srctime == GT &&
         compareClockTime iotime srctime == GT
        then fmap Just (readTypes opts mname)
        else return Nothing

-- Reads constructors, non-trivial call types, and
-- non-trivial input/output types for a given module.
readTypes :: Options -> String
          -> IO ([[(QName,Int)]], [(QName,[[CallType]])], [(QName,InOutType)])
readTypes _ mname = do
  conss <- readFile (consTypesFile mname) >>= return . read
  cts   <- readFile (callTypesFile mname) >>= return . map read . lines
  iots  <- readFile (ioTypesFile   mname) >>= return . map read . lines
  return (conss,
          map (\ (fn,ct) -> ((mname,fn), ct)) cts,
          map (\ (fn,iot) -> ((mname,fn), IOT iot)) iots)

--- Reads constructors, non-trivial call types, and
--- non-trivial input/output types for a given list of modules.
--- If some of the data files do not exists or are not newer
--- than the module source, the operation provided as the second argument
--- is applied before reading the files.
readTypesOfModules :: Options -> (Options -> String -> IO ()) -> [String]
  -> IO ([[(QName,Int)]], [(QName,[[CallType]])], [(QName,InOutType)])
readTypesOfModules opts computetypes mnames = do
  (xs,ys,zs) <- mapM tryRead mnames >>= return . unzip3
  return (concat xs, concat ys, concat zs)
 where
  tryRead mname =
    tryReadTypes opts mname >>=
    maybe (do printWhenStatus opts $
                "\nVerifying imported module '" ++ mname ++ "'..."
              computetypes opts mname
              tryReadTypes opts mname >>=
                maybe (error $ "Cannot read call/io types of module '" ++
                               mname ++ "'")
                      return)
          return

--- Reads the possibly previously inferred call types for a given module
--- if it is up-to-date (where the modification time of the module
--- is passed as the second argument).
readCallTypeFile :: Options -> ClockTime -> String
                 -> IO (Maybe [(QName,[[CallType]])])
readCallTypeFile opts mtimesrc mname = do
  let fname = callTypesFile mname
  existsf <- doesFileExist fname
  if existsf && not (optRerun opts)
    then do
      mtimectf <- getModificationTime fname
      if compareClockTime mtimectf mtimesrc == GT
        then do
          printWhenStatus opts $
            "Reading previously inferred call types from '" ++ fname ++ "'..."
          cts <- readFile fname >>= return . map read . lines
          return $ Just (map (\ (fn,ct) -> ((mname,fn), ct)) cts)
        else return Nothing
    else return Nothing

------------------------------------------------------------------------------
------------------------------------------------------------------------------
--- Reads the public non-trivial call types (which have been already
--- computed or explicitly specified) for a given module which are
--- stored in the source directory of the module with module suffix
--- `_CALLTYPES`.
--- If the file does not exist, try to read a file from the `include`
--- directory (for standard libraries).
readPublicCallTypeModule :: Options -> [[(QName,Int)]] -> ClockTime -> String
                         -> IO [(QName,[[CallType]])]
readPublicCallTypeModule opts allcons mtimesrc mname = do
  let specmname = callTypesModule mname
  specfile <- lookupModuleSourceInLoadPath specmname >>= return . maybe "" snd
  existsf <- doesFileExist specfile
  if existsf && not (optRerun opts)
    then do
      mtimesf <- getModificationTime specfile
      if compareClockTime mtimesf mtimesrc == GT
        then do
          printWhenStatus opts $
            "Reading required call types from '" ++ specfile ++ "'..."
          readCallTypeSpecMod allcons mname specmname
        else do
          printWhenStatus opts $
           "Ignoring call type specifications in '" ++ specfile ++ "' (too old)"
          tryReadInclude specmname
    else tryReadInclude specmname
 where
  tryReadInclude ctmname = do
    pkgpath <- getPackagePath
    let ifname = pkgpath </> "include" </> modNameToPath ctmname ++ ".curry"
    existsif <- doesFileExist ifname
    if existsif
      then do
        printWhenStatus opts $
          "Reading required call types from '" ++ ifname ++ "'..."
        curdir <- getCurrentDirectory
        setCurrentDirectory $ pkgpath </> "include"
        result <- readCallTypeSpecMod allcons mname ctmname
        setCurrentDirectory curdir
        return result
      else return []


--- Reads a call type specificaiton file for a module.
--- if it is up-to-date (where the modification time of the module
--- is passed as the second argument).
readCallTypeSpecMod :: [[(QName,Int)]] -> String -> String
                    -> IO [(QName,[[CallType]])]
readCallTypeSpecMod allcons mname specmname = do
  smod <- readCurry specmname
  return (map (fromSpecFunc allcons mname) (filter isSpecFunc (functions smod)))
 where
  isSpecFunc fd = "'calltype" `isSuffixOf` snd (funcName fd)

maybeCons2CallTypes :: [[(QName,Int)]] -> [[Maybe [String]]]
                    -> [[CallType]]
maybeCons2CallTypes allcons cts = map (map mb2ct) cts
 where
  mb2ct Nothing       = AnyT
  mb2ct (Just cscts)  = MCons $ map (mb2cs . readQC) cscts
   where
    mb2cs qc = (qc, take (arityOfCons allcons qc) (repeat AnyT))

fromSpecFunc :: [[(QName,Int)]] -> String -> CFuncDecl -> (QName, [[CallType]])
fromSpecFunc allcons mname fdecl =
  ((mname,fname),
   maybeCons2CallTypes allcons $ rules2calltype (funcRules fdecl))
 where
  fname = fromSpecName (decodeContractName (snd (funcName fdecl)))

  fromSpecName = reverse . drop 9 . reverse

  rules2calltype rl = case rl of
    [CRule [] (CSimpleRhs exp [])] -> parseACList parseACTuple exp
    _                              -> error syntaxError

  syntaxError =
    "Illegal specification syntax in specification rule for '" ++ fname ++ "'"

  parseACTuple exp = case funArgsOfExp exp of
    Just (qf,[])   | qf == pre "()" -> []
    Just (qf,args) | "(," `isPrefixOf` snd qf
                  -> map (parseACMaybe (parseACList parseACString)) args
    _             -> [parseACMaybe (parseACList parseACString) exp]

  parseACMaybe parsex exp = case funArgsOfExp exp of
    Just (qf,[])  | qf == pre "Nothing" -> Nothing
    Just (qf,[a]) | qf == pre "Just"    -> Just (parsex a)
    _ -> error syntaxError

  parseACList parsex exp = case funArgsOfExp exp of
    Just (qf,[])      | qf == pre "[]" -> []
    Just (qf,[e1,e2]) | qf == pre ":"  -> parsex e1 : parseACList parsex e2
    _                                  -> error syntaxError

  parseACString exp = case exp of
    CLit (CStringc s) -> s
    _                 -> error syntaxError


funArgsOfExp :: CExpr -> Maybe (QName,[CExpr])
funArgsOfExp exp = case exp of
  CSymbol qf   -> Just (qf,[])
  CApply e1 e2 ->  maybe Nothing
                         (\ (qf, args) -> Just (qf, args ++ [e2]))
                         (funArgsOfExp e1)
  _            -> Nothing

------------------------------------------------------------------------------
--- Transforms call types to AbstractCurry functions which can be read
--- with `readCallTypeSpecMod`.

--- Writes a Curry module file containing the non-trivial call types
--- of a given module so that it can be read back with
--- `readCallTypeSpecMod`.
writeCallTypeSpecMod :: Options -> String -> [(QName,[[CallType]])] -> IO ()
writeCallTypeSpecMod opts mname pubntcalltypes = do
  let ctmname = callTypesModule mname
      ctfile  = callTypesDataDir </> modNameToPath ctmname ++ ".curry"
  createDirectoryIfMissing True (dropFileName ctfile)
  exct <- doesFileExist ctfile
  if null pubntcalltypes
    then when exct $ removeFile ctfile
    else do
      oldctmod <- if exct then readCompleteFile ctfile else return ""
      let ctmod = showCProg (callTypes2SpecMod mname pubntcalltypes) ++ "\n"
      unless (oldctmod == ctmod || not (optWrite opts)) $ do
        writeFile ctfile ctmod
        includepath <- fmap (</> "include") getPackagePath
        printWhenStatus opts $
          "A Curry module '" ++ ctmname ++
          "' with required call types is written to\n'" ++ ctfile ++ "'.\n" ++
          "To use it for future verifications, store it\n" ++
          "- either in the source directory of module '" ++ mname ++ "'\n" ++
          "- or under '" ++ includepath ++ "'"

--- Transforms call types to an AbstractCurry module which can be read
--- with `readCallTypeSpecMod`.
callTypes2SpecMod :: String -> [(QName,[[CallType]])] -> CurryProg
callTypes2SpecMod mname functs =
  simpleCurryProg specmname [] [] (map ct2fun functs) []
 where
  specmname = callTypesModule mname

  ct2fun ((_,fn), cts) =
    cmtfunc
      ("Required call type of operation `" ++ fn ++ "`:")
      (specmname, encodeContractName $ fn ++ "'calltype") 0 Public
      --(emptyClassType (listType (tupleType (take ar (repeat maybeConsType)))))
      (emptyClassType (baseType (pre "untyped")))
      [simpleRule [] (list2ac (map (tupleExpr . map ct2mb) cts))]
   where
    --ar = if null cts then 0 else length (head cts) -- arity of the function
    --maybeConsType = maybeType (listType (tupleType [stringType, intType]))

  ct2mb AnyT          = constF (pre "Nothing")
  ct2mb (MCons cscts) = applyJust (list2ac $ map cs2mb cscts)

  cs2mb ct@((mn,mc),cts) =
    if any (/= AnyT) cts
      then error $ "Call type with nested constructors: " ++ show ct
      else string2ac $ (if null mn then "" else mn ++ ".") ++ mc

------------------------------------------------------------------------------

