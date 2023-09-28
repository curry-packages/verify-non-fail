------------------------------------------------------------------------------
--- Operations to write and read auxiliary files containing
--- verification information.
--- 
--- The tool caches already computed analysis results about modules
--- under the directory defined in `getVerifyCacheDirectory` which
--- is usually `~/.curry_verifycache/...`.
---
--- @author Michael Hanus
--- @version September 2023
-----------------------------------------------------------------------------

module Verify.Files
   ( deleteVerifyCacheDirectory
   , readTypesOfModules, readPublicCallTypeModule, readCallTypeFile
   , storeTypes
   )
  where

import Control.Monad        ( unless, when )
import Data.List            ( intercalate, isPrefixOf, isSuffixOf, sortBy )

import Curry.Compiler.Distribution ( installDir )

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
import System.FilePath      ( (</>), (<.>), dropDrive, dropFileName, isAbsolute
                            , joinPath, splitDirectories )
import System.IOExts        ( evalCmd, readCompleteFile )
import System.Process       ( system )

import PackageConfig        ( getPackagePath )
import Verify.CallTypes
import Verify.Helpers
import Verify.IOTypes
import Verify.Options

------------------------------------------------------------------------------
-- Definition of directory and file names for various data.

-- Cache directory where data files generated and used by this tool are stored.
-- If $HOME exists, it is `~/.curryverify_cache/<CURRYSYSTEM>`.
getVerifyCacheDirectory :: IO String
getVerifyCacheDirectory = do
  homedir    <- getHomeDirectory
  hashomedir <- doesDirectoryExist homedir
  let maindir = if hashomedir then homedir else installDir
  return $ maindir </> ".curry_verifycache" </>
           joinPath (tail (splitDirectories currySubdir))

--- Delete the tool's cache directory (for the Curry system).
deleteVerifyCacheDirectory :: Options -> IO ()
deleteVerifyCacheDirectory opts = do
  cachedir <- getVerifyCacheDirectory
  exists   <- doesDirectoryExist cachedir
  when exists $ do
    printWhenStatus opts $ "Deleting directory '" ++ cachedir ++ "''..."
    system ("rm -Rf " ++ quote cachedir)
    return ()
 where
  quote s = "\"" ++ s ++ "\""

--- Get the file name in which analysis results for a given module
--- (first argument) which can be found in the load path are stored.
--- The second argument is a key for the type of analysis information
--- which is the suffix of the file name.
getVerifyCacheBaseFile :: String -> String -> IO String
getVerifyCacheBaseFile moduleName infotype = do
  analysisDirectory <- getVerifyCacheDirectory
  let modAnaName = moduleName ++ "-" ++ infotype
  (fileDir,_) <- findModuleSourceInLoadPath moduleName
  absfileDir  <- getRealPath fileDir
  return $ analysisDirectory </> dropDrive absfileDir </> modAnaName
 where
  findModuleSourceInLoadPath modname =
    lookupModuleSourceInLoadPath modname >>=
    maybe (error $ "Source file for module '" ++ modname ++ "' not found!")
          return

--- Returns the absolute real path for a given file path
--- by following all symlinks in all path components.
getRealPath :: String -> IO String
getRealPath path = do
  (rc, out, _) <- evalCmd "realpath" [path] ""
  if rc == 0 then return (stripSpaces out)
             else getAbsolutePath path
 where
  stripSpaces = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- Gets the name of the file containing all call types of a module.
getCallTypesFile :: String -> IO String
getCallTypesFile mname = getVerifyCacheBaseFile mname "CALLTYPES"

-- Gets the name of the file containing all input/output types of a module.
getIOTypesFile :: String -> IO String
getIOTypesFile mname = getVerifyCacheBaseFile mname "IOTYPES"

-- Gets the name of the file containing all constructor of a module.
getConsTypesFile :: String -> IO String
getConsTypesFile mname = getVerifyCacheBaseFile mname "CONSTYPES"

-- The name of the Curry module where the call type specifications are stored.
callTypesModule :: String -> String
callTypesModule mname = mname ++ "_CALLTYPES"

------------------------------------------------------------------------------
-- Stores call types and input/output types for a module.
storeTypes :: Options -> String -> [[(QName,Int)]]
           -> [(QName,[[CallType]])] -- public non-trivial call types
           -> [(QName,[[CallType]])] -- all call types
           -> [(QName,InOutType)]    -- all input output types
           -> IO ()
storeTypes opts mname allcons pubntcalltypes calltypes iotypes = do
  patfile <- getVerifyCacheBaseFile mname "..."
  printWhenAll opts $ "Storing analysis results at '" ++ patfile ++ "'"
  createDirectoryIfMissing True (dropFileName patfile)
  csfile <- getConsTypesFile mname
  ctfile <- getCallTypesFile mname
  iofile <- getIOTypesFile   mname
  writeFile csfile (show allcons)
  writeFile ctfile
    (unlines (map (\ ((_,fn),ct) -> show (fn,ct)) (filterMod calltypes)))
  writeFile iofile
    (unlines (map (\ ((_,fn), IOT iots) -> show (fn,iots)) (filterMod iotypes)))
  when (optModule opts) $
    writeCallTypeSpecMod opts mname (sortFunResults pubntcalltypes)
 where
  filterMod xs = filter (\ ((mn,_),_) -> mn == mname) xs

-- Try to read constructors, call types, and
-- input/output types for a given module.
-- If the data files do not exist or are older than the source of the
-- module, `Nothing` is returned.
tryReadTypes :: Options -> String
  -> IO (Maybe ([[(QName,Int)]], [(QName,[[CallType]])], [(QName,InOutType)]))
tryReadTypes opts mname = do
  csfile <- getConsTypesFile mname
  ctfile <- getCallTypesFile mname
  iofile <- getIOTypesFile   mname
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

-- Reads constructors, call types, and input/output types for a given module.
readTypes :: Options -> String
          -> IO ([[(QName,Int)]], [(QName,[[CallType]])], [(QName,InOutType)])
readTypes _ mname = do
  csfile <- getConsTypesFile mname
  ctfile <- getCallTypesFile mname
  iofile <- getIOTypesFile   mname
  conss  <- readFile csfile >>= return . read
  cts    <- readFile ctfile >>= return . map read . lines
  iots   <- readFile iofile >>= return . map read . lines
  return (conss,
          map (\ (fn,ct) -> ((mname,fn), ct)) cts,
          map (\ (fn,iot) -> ((mname,fn), IOT iot)) iots)

--- Reads constructors, call types, and input/output types
--- for a given list of modules.
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
  fname <- getCallTypesFile mname
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


--- Reads a call type specification file for a module
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
      ctfile  = ctmname ++ ".curry"
  exct <- doesFileExist ctfile
  if null pubntcalltypes
    then when exct $ removeFile ctfile
    else do
      oldctmod <- if exct then readCompleteFile ctfile else return ""
      let ctmod = showCProg (callTypes2SpecMod mname pubntcalltypes) ++ "\n"
      unless (oldctmod == ctmod || not (optModule opts)) $ do
        writeFile ctfile ctmod
        includepath <- fmap (</> "include") getPackagePath
        printWhenStatus opts $
          "A Curry module '" ++ ctmname ++
          "' with required call types is written to\n'" ++ ctfile ++ "'.\n" ++
          "To use it for future verifications, store this module\n" ++
          "- either under '" ++ includepath ++ "'\n" ++
          "- or in the source directory of module '" ++ mname ++ "'\n"

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

