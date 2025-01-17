------------------------------------------------------------------------------
--- Operations to write and read auxiliary files containing
--- verification information.
--- 
--- The tool caches already computed analysis results about modules
--- under the directory defined in `getVerifyCacheDirectory` which
--- is usually `~/.curry_verify_cache/<CURRYSYSTEM>/...`.
---
--- @author Michael Hanus
--- @version January 2025
-----------------------------------------------------------------------------

module Verify.Files
   ( deleteVerifyCacheDirectory, typeFilesOutdated, readCallCondTypes
   , readTypesOfModules, readPublicCallTypeModule
   , readCallTypeFile, readNonFailCondFile
   , storeTypes
   )
  where

import Control.Monad        ( unless, when )
import Data.List            ( find, intercalate, isPrefixOf, isSuffixOf, sortBy )

import Curry.Compiler.Distribution ( installDir )

import AbstractCurry.Build
import AbstractCurry.Files  ( readCurry )
import AbstractCurry.Pretty ( showCProg )
import AbstractCurry.Select
import AbstractCurry.Types hiding ( pre )
import Analysis.TermDomain  ( TermDomain )
import Contract.Names       ( decodeContractName, encodeContractName )
import Data.Time            ( ClockTime, compareClockTime )
import Debug.Profile
import FlatCurry.Types      ( FuncDecl )
import FlatCurry.TypesRW
import RW.Base              ( ReadWrite, readDataFile, writeDataFile )
import System.CurryPath     ( currySubdir, lookupModuleSourceInLoadPath
                            , modNameToPath )
import System.Directory
import System.FilePath      ( (</>), (<.>), dropDrive, dropFileName, isAbsolute
                            , joinPath, splitDirectories )
import System.IO            -- for ReadWrite instances
import System.IOExts        ( evalCmd, readCompleteFile )
import System.Process       ( system )

import FlatCurry.Build      ( pre )
import PackageConfig        ( getPackagePath )
import Verify.CallTypes
import Verify.Helpers
import Verify.IOTypes
import Verify.NonFailConditions
import Verify.Options
import Verify.ProgInfo

------------------------------------------------------------------------------
-- Definition of directory and file names for various data.

-- Cache directory where data files generated and used by this tool are stored.
-- If $HOME exists, it is `~/.curry_verify_cache/<CURRYSYSTEM>/<DOMAINID>`.
getVerifyCacheDirectory :: String -> IO String
getVerifyCacheDirectory domainid = do
  homedir    <- getHomeDirectory
  hashomedir <- doesDirectoryExist homedir
  let maindir = if hashomedir then homedir else installDir
  return $ maindir </> ".curry_verify_cache" </>
           joinPath (tail (splitDirectories currySubdir)) </> domainid

--- Delete the tool's cache directory (for the Curry system).
deleteVerifyCacheDirectory :: Options -> IO ()
deleteVerifyCacheDirectory opts = do
  cachedir <- getVerifyCacheDirectory (optDomainID opts)
  exists   <- doesDirectoryExist cachedir
  when exists $ do
    printWhenStatus opts $ "Deleting directory '" ++ cachedir ++ "''..."
    system $ "rm -Rf " ++ quote cachedir
    return ()
 where
  quote s = "\"" ++ s ++ "\""

--- Get the file name in which analysis results for a given module
--- (first argument) which can be found in the load path are stored.
--- The second argument is a key for the type of analysis information
--- which is the suffix of the file name.
getVerifyCacheBaseFile :: Options -> String -> String -> IO String
getVerifyCacheBaseFile opts moduleName infotype = do
  analysisDirectory <- getVerifyCacheDirectory (optDomainID opts)
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

-- Gets the name of the file containing all abstract call types of a module.
getCallTypesFile :: Options -> String -> IO String
getCallTypesFile opts mname = getVerifyCacheBaseFile opts mname "CALLTYPES"

-- Gets the name of the file containing non-fail conditions of a module.
getNonFailCondFile :: Options -> String -> IO String
getNonFailCondFile opts mname = getVerifyCacheBaseFile opts mname "NONFAIL"

-- Gets the name of the file containing all input/output types of a module.
getIOTypesFile :: Options -> String -> IO String
getIOTypesFile opts mname = getVerifyCacheBaseFile opts mname "IOTYPES"

-- Gets the name of the file containing all constructor information of a module.
getConsInfosFile :: Options -> String -> IO String
getConsInfosFile opts mname = getVerifyCacheBaseFile opts mname "CONSINFOS"

-- The name of the Curry module where the call type specifications are stored.
callTypesModule :: String -> String
callTypesModule mname = mname ++ "_CALLSPEC"

------------------------------------------------------------------------------
--- Stores constructores, call types, non-fail conditions
---  and input/output types for a module.
storeTypes :: TermDomain a => Options
           -> String                 -- module name
           -> [FuncDecl]             -- functions of the module
           -> [(QName,ConsInfo)]     -- information about all constructors
           -> [(QName,ACallType a)]  -- all inferred abstract call types
           -> [(QName,ACallType a)]  -- public non-trivial abstract call types
           -> [(QName,NonFailCond)]  -- inferred non-fail conditions
           -> [(QName,InOutType a)]  -- all input output types
           -> IO ()
storeTypes opts mname fdecls consinfos acalltypes pubntcalltypes funconds
           iotypes = do
  patfile <- getVerifyCacheBaseFile opts mname "..."
  printWhenAll opts $ "Caching analysis results at '" ++ patfile ++ "'"
  createDirectoryIfMissing True (dropFileName patfile)
  cifile  <- getConsInfosFile   opts mname
  ctfile  <- getCallTypesFile   opts mname
  nffile  <- getNonFailCondFile opts mname
  iofile  <- getIOTypesFile     opts mname
  writeTermFile opts cifile consinfos
  writeTermFile opts ctfile
    (map (\ ((_,fn),ct) -> (fn,ct)) (filterMod acalltypes))
  writeTermFile opts nffile
    (map (\ ((_,fn),ct) -> (fn, filterUnknownTypes ct)) (filterMod funconds))
  writeTermFile opts iofile
    (map (\ ((_,fn), IOT iots) -> (fn,iots)) (filterMod iotypes))
  when (optSpecModule opts) $
    writeSpecModule opts mname fdecls (sortFunResults pubntcalltypes)
                    (sortFunResults funconds)
 where
  -- Filter typed variables with unknown types from a non-fail condition
  -- (these are usually pattern variables) to avoid type inference problems
  -- for them.
  -- (A better solution would be the removal of all case pattern variables.)
  filterUnknownTypes :: NonFailCond -> NonFailCond
  filterUnknownTypes (vts,e) = (filter ((/=unknownType) . snd) vts, e)
  
  filterMod xs = filter (\ ((mn,_),_) -> mn == mname) xs

-- Check whether the files of constructors, call types, non-fail conditions, and
-- input/output types for a given module are outdated, i.e., might not exist
-- or are older than the source of the module.
typeFilesOutdated :: Options -> String -> IO Bool
typeFilesOutdated opts mname = do
  cifile   <- getConsInfosFile   opts mname
  ctfile   <- getCallTypesFile   opts mname
  nffile   <- getNonFailCondFile opts mname
  iofile   <- getIOTypesFile     opts mname
  allexists <- fmap and $ mapM doesFileExist [cifile,ctfile,nffile,iofile]
  if not allexists
    then return True
    else do
      srctime <- getModuleModTime mname
      ftimes  <- mapM getModificationTime [cifile,ctfile,nffile,iofile]
      return $ any (\t -> compareClockTime t srctime == LT) ftimes

-- Reads constructors, abstract call types, non-fail conditions,
-- and input/output types for a given module.
readTypes :: TermDomain a => Options -> String
          -> IO ([(QName,ConsInfo)], [(QName,ACallType a)],
                 [(QName,NonFailCond)], [(QName,InOutType a)])
readTypes opts mname = do
  consis <- getConsInfosFile   opts mname >>= readTermFile opts
  cts    <- getCallTypesFile   opts mname >>= readTermFile opts
  nfcs   <- getNonFailCondFile opts mname >>= readTermFile opts
  iots   <- getIOTypesFile     opts mname >>= readTermFile opts
  return (consis,
          map (\ (fn,ct)  -> ((mname,fn), ct)) cts,
          map (\ (fn,nfc) -> ((mname,fn), nfc)) nfcs,
          map (\ (fn,iot) -> ((mname,fn), IOT iot)) iots)

-- Reads the abstract call types and non-fail conditions
-- for a given module.
readCallCondTypes :: TermDomain a => Options -> String
                  -> IO ([(QName,ACallType a)], [(QName,NonFailCond)])
readCallCondTypes opts mname = do
  cts    <- getCallTypesFile   opts mname >>= readTermFile opts
  nfcs   <- getNonFailCondFile opts mname >>= readTermFile opts
  return (map (\ (fn,ct)  -> ((mname,fn), ct)) cts,
          map (\ (fn,nfc) -> ((mname,fn), nfc)) nfcs)

--- Reads constructors, call types, non-fail conditions, and input/output types
--- for a given list of modules.
--- If some of the data files does not exist or is not newer
--- than the module source, the operation provided as the second argument
--- is applied before reading the files.
readTypesOfModules :: TermDomain a => Options
  -> (Options -> String -> IO ()) -> [String]
  -> IO ([(QName,ConsInfo)], [(QName, ACallType a)],
         [(QName,NonFailCond)], [(QName, InOutType a)])
readTypesOfModules opts computetypes mnames = do
  (xs,ys,zs,ws) <- mapM tryRead mnames >>= return . unzip4
  return (concat xs, concat ys, concat zs, concat ws)
 where
  tryRead mname = do
    outdated <- typeFilesOutdated opts mname
    if outdated
      then do
        printWhenStatus opts $ "\nVerifying imported module '" ++ mname ++ "'..."
        computetypes opts mname
        oldfs <- typeFilesOutdated opts mname
        if oldfs
          then error $ "Cannot read call/io types of module '" ++ mname ++ "'"
          else readTypes opts mname
      else readTypes opts mname

--- Transforms a list of quadruples into a quadruple of lists.
unzip4 :: [(a, b, c, d)] -> ([a], [b], [c], [d])
unzip4 []             = ([], [], [], [])
unzip4 ((x, y, z, w) : ts) = (x : xs, y : ys, z : zs, w : ws)
 where (xs, ys, zs, ws) = unzip4 ts

--- Reads the possibly previously inferred abstract call types for a
--- given module if it is up-to-date (where the modification time
--- of the module is passed as the second argument).
readCallTypeFile :: TermDomain a => Options -> ClockTime -> String
                 -> IO (Maybe [(QName,ACallType a)])
readCallTypeFile opts mtimesrc mname = do
  fname <- getCallTypesFile opts mname
  existsf <- doesFileExist fname
  if existsf && not (optRerun opts)
    then do
      mtimectf <- getModificationTime fname
      if compareClockTime mtimectf mtimesrc == GT
        then do
          printWhenStatus opts $
            "Reading previously inferred abstract call types from '" ++
            fname ++ "'..."
          cts <- readTermFile opts fname
          return $ Just (map (\ (fn,ct) -> ((mname,fn), ct)) cts)
        else return Nothing
    else return Nothing

--- Reads the possibly previously inferred non-fail conditions for a
--- given module if it is up-to-date (where the modification time
--- of the module is passed as the second argument).
readNonFailCondFile :: Options -> ClockTime -> String
                    -> IO (Maybe [(QName,NonFailCond)])
readNonFailCondFile opts mtimesrc mname = do
  fname <- getNonFailCondFile opts mname
  existsf <- doesFileExist fname
  if existsf && not (optRerun opts)
    then do
      mtimectf <- getModificationTime fname
      if compareClockTime mtimectf mtimesrc == GT
        then do
          printWhenStatus opts $
            "Reading previously inferred non-fail conditions from '" ++
            fname ++ "'..."
          cts <- readTermFile opts fname
          return $ Just $ map (\ (fn,ct) -> ((mname,fn), ct)) cts
        else return Nothing
    else return Nothing

------------------------------------------------------------------------------
--- Reads the public non-trivial call types (which have been already
--- computed or explicitly specified) for a given module which are
--- stored in the source directory of the module with module suffix
--- `_CALLTYPES`.
--- If the file does not exist, try to read a file from the `include`
--- directory (for standard libraries).
readPublicCallTypeModule :: Options -> [(QName,ConsInfo)] -> ClockTime -> String
                         -> IO [(QName,[[CallType]])]
readPublicCallTypeModule opts consinfos mtimesrc mname = do
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
          readCallTypeSpecMod consinfos mname specmname
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
        result <- readCallTypeSpecMod consinfos mname ctmname
        setCurrentDirectory curdir
        return result
      else return []


--- Reads a call type specification file for a module
--- if it is up-to-date (where the modification time of the module
--- is passed as the second argument).
readCallTypeSpecMod :: [(QName,ConsInfo)] -> String -> String
                    -> IO [(QName,[[CallType]])]
readCallTypeSpecMod consinfos mname specmname = do
  smod <- readCurry specmname
  return $ map (fromSpecFunc consinfos mname)
               (filter isSpecFunc (functions smod))
 where
  isSpecFunc fd = "'calltype" `isSuffixOf` snd (funcName fd)

maybeCons2CallTypes :: [(QName,ConsInfo)] -> [[Maybe [String]]]
                    -> [[CallType]]
maybeCons2CallTypes consinfos cts = map (map mb2ct) cts
 where
  mb2ct Nothing       = AnyT
  mb2ct (Just cscts)  = MCons $ map (mb2cs . readQC) cscts
   where
    mb2cs qc = (qc, take (arityOfCons consinfos qc) (repeat AnyT))

fromSpecFunc :: [(QName,ConsInfo)] -> String -> CFuncDecl
             -> (QName, [[CallType]])
fromSpecFunc consinfos mname fdecl =
  ((mname,fname),
   maybeCons2CallTypes consinfos $ rules2calltype (funcRules fdecl))
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
writeSpecModule :: TermDomain a => Options -> String -> [FuncDecl]
                -> [(QName,ACallType a)] -> [(QName,NonFailCond)] -> IO ()
writeSpecModule opts mname fdecls pubntcalltypes funconds = do
  let ctmname = callTypesModule mname
      ctfile  = ctmname ++ ".curry"
  exct <- doesFileExist ctfile
  if null pubntcalltypes && null funconds
    then when exct $ removeFile ctfile
    else do
      oldctmod <- if exct then readCompleteFile ctfile else return ""
      let ctmod = callTypeCond2SpecMod mname fdecls pubntcalltypes funconds
      unless (oldctmod == ctmod || not (optSpecModule opts)) $ do
        writeFile ctfile ctmod
        printWhenStatus opts $
          "A Curry module '" ++ ctmname ++ "' with required call types\n" ++
          "and non-fail conditions is written to: '" ++ ctfile ++ "'.\n" -- ++

--- Transforms call types and non-fail condition into human-readable
--- Curry programan.
callTypeCond2SpecMod :: TermDomain a => String -> [FuncDecl]
                     -> [(QName,ACallType a)] -> [(QName,NonFailCond)] -> String
callTypeCond2SpecMod mname fdecls functs funconds =
  showCProg (simpleCurryProg specmname [] []
                             (map ct2fun (filter hasNoNFCond functs)) []) ++
  "\n" ++ showConditions fdecls funconds
 where
  specmname = callTypesModule mname

  hasNoNFCond = (`notElem` (map fst funconds)) . fst

  ct2fun ((_,fn), cts) =
    cmtfunc
      ("Required call type of operation `" ++ fn ++ "` (pretty printed):")
      (specmname, encodeContractName $ fn ++ "'calltype") 0 Public
      (emptyClassType stringType)
      [simpleRule [] (string2ac (prettyFunCallAType cts))]

------------------------------------------------------------------------------
--- Transforms call types to an AbstractCurry module which can be read
--- with `readCallTypeSpecMod` (deprecated)
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
-- Writes a list of data terms into a file together with another file
-- (with suffix `.rw`) containing a compact representation.
writeTermFile :: (ReadWrite a, Show a) => Options -> String -> a -> IO ()
writeTermFile _ f ts = do
  writeFile f (show ts)          -- store terms as strings
  writeDataFile (f <.> "rw") ts  -- store terms as compact data

--- Reads a file containing a list of terms. Try to read compact representation
--- if it exists and is not older than the terms file.
--- If the first argument is `True`, read also the term file and report
--- the timings of reading this file and the compact data file.
readTermFile :: (Read a, ReadWrite a, Eq a) => Options -> String -> IO a
readTermFile opts file = do
  let reporttimings = optVerb opts > 3
      rwfile = file <.> "rw"
      readtermfile = fmap read $ readFile file
  rwex <- doesFileExist rwfile
  if rwex
    then do
      ftime   <- getModificationTime file
      rwftime <- getModificationTime rwfile
      if compareClockTime rwftime ftime == LT
        then readtermfile
        else do
          (mbterms,rwtime) <- getElapsedTimeNF (readDataFile rwfile)
          maybe (error $ "Illegal data in file " ++ rwfile)
                (\rwterms ->
                  if not reporttimings
                    then return rwterms
                    else do
                      printInfoLine $ "\nReading " ++ file
                      (terms,ttime) <- getElapsedTimeNF readtermfile
                      printInfoLine $ "Time: " ++ show ttime ++
                                      " msecs / Compact reading: " ++
                                      show rwtime ++ " msecs / speedup: " ++
                                      show (fromInt ttime / fromInt rwtime)
                      if rwterms == terms -- safety check
                        then return rwterms
                        else error "Difference in compact terms!" )
                mbterms
    else readtermfile

------------------------------------------------------------------------------
