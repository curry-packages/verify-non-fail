------------------------------------------------------------------------------
--- Operations to write and read auxiliary files containing
--- verification information.
--- 
--- The tool caches already computed analysis results about modules
--- under the directory defined in `getVerifyCacheDirectory` which
--- is usually `~/.curry_verifycache/...`.
---
--- @author Michael Hanus
--- @version December 2023
-----------------------------------------------------------------------------

module Verify.Files
   ( deleteVerifyCacheDirectory
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
import FlatCurry.Types      ( FuncDecl )
import System.CurryPath     ( currySubdir, lookupModuleSourceInLoadPath
                            , modNameToPath )
import System.Directory
import System.FilePath      ( (</>), (<.>), dropDrive, dropFileName, isAbsolute
                            , joinPath, splitDirectories )
import System.IOExts        ( evalCmd, readCompleteFile )
import System.Process       ( system )

import FlatCurry.Build      ( pre )
import PackageConfig        ( getPackagePath )
import Verify.CallTypes
import Verify.Helpers
import Verify.IOTypes
import Verify.NonFailConditions
import Verify.Options

------------------------------------------------------------------------------
-- Definition of directory and file names for various data.

-- Cache directory where data files generated and used by this tool are stored.
-- If $HOME exists, it is `~/.curryverify_cache/<CURRYSYSTEM>`.
getVerifyCacheDirectory :: String -> IO String
getVerifyCacheDirectory domainid = do
  homedir    <- getHomeDirectory
  hashomedir <- doesDirectoryExist homedir
  let maindir = if hashomedir then homedir else installDir
  return $ maindir </> ".curry_verifycache" </> domainid </>
           joinPath (tail (splitDirectories currySubdir))

--- Delete the tool's cache directory (for the Curry system).
deleteVerifyCacheDirectory :: Options -> IO ()
deleteVerifyCacheDirectory opts = do
  cachedir <- getVerifyCacheDirectory (optDomainID opts)
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

-- Gets the name of the file containing all constructor of a module.
getConsTypesFile :: Options -> String -> IO String
getConsTypesFile opts mname = getVerifyCacheBaseFile opts mname "CONSTYPES"

-- The name of the Curry module where the call type specifications are stored.
callTypesModule :: String -> String
callTypesModule mname = mname ++ "_CALLSPEC"

------------------------------------------------------------------------------
--- Stores constructores, call types, non-fail conditions
---  and input/output types for a module.
storeTypes :: TermDomain a => Options
           -> String                 -- module name
           -> [FuncDecl]             -- functions of the module
           -> [[(QName,Int)]]        -- all constructors grouped by type
           -> [(QName,ACallType a)]  -- all inferred abstract call types
           -> [(QName,ACallType a)]  -- public non-trivial abstract call types
           -> [(QName,NonFailCond)]  -- inferred non-fail conditions
           -> [(QName,InOutType a)]  -- all input output types
           -> IO ()
storeTypes opts mname fdecls allcons acalltypes pubntcalltypes funconds
           iotypes = do
  patfile <- getVerifyCacheBaseFile opts mname "..."
  printWhenAll opts $ "Caching analysis results at '" ++ patfile ++ "'"
  createDirectoryIfMissing True (dropFileName patfile)
  csfile  <- getConsTypesFile   opts mname
  ctfile  <- getCallTypesFile   opts mname
  nffile  <- getNonFailCondFile opts mname
  iofile  <- getIOTypesFile     opts mname
  writeFileAndReport csfile (show allcons)
  writeFileAndReport ctfile
    (unlines (map (\ ((_,fn),ct) -> show (fn,ct)) (filterMod acalltypes)))
  writeFileAndReport nffile
    (unlines (map (\ ((_,fn),ct) -> show (fn,ct)) (filterMod funconds)))
  writeFileAndReport iofile
    (unlines (map (\ ((_,fn), IOT iots) -> show (fn,iots)) (filterMod iotypes)))
  when (optSpecModule opts) $
    writeSpecModule opts mname fdecls (sortFunResults pubntcalltypes)
                    (sortFunResults funconds)
 where
  writeFileAndReport f s = do
    when (optVerb opts > 3) $ putStr $ "Writing cache file '" ++ f ++ "'..."
    writeFile f s
    printWhenAll opts "done"
  
  filterMod xs = filter (\ ((mn,_),_) -> mn == mname) xs

-- Try to read constructors, call types, non-fail conditions, and
-- input/output types for a given module.
-- If the data files do not exist or are older than the source of the
-- module, `Nothing` is returned.
tryReadTypes :: TermDomain a => Options -> String
  -> IO (Maybe ([[(QName,Int)]], [(QName,ACallType a)],
                 [(QName,NonFailCond)], [(QName,InOutType a)]))
tryReadTypes opts mname = do
  csfile   <- getConsTypesFile   opts mname
  ctfile   <- getCallTypesFile   opts mname
  nffile   <- getNonFailCondFile opts mname
  iofile   <- getIOTypesFile     opts mname
  csexists <- doesFileExist csfile
  ctexists <- doesFileExist ctfile
  nfexists <- doesFileExist nffile
  ioexists <- doesFileExist iofile
  if not (csexists && ctexists && ioexists && nfexists)
    then return Nothing
    else do
      srctime <- getModuleModTime mname
      cstime  <- getModificationTime csfile
      cttime  <- getModificationTime ctfile
      nftime  <- getModificationTime nffile
      iotime  <- getModificationTime iofile
      if compareClockTime cstime srctime == GT &&
         compareClockTime cttime srctime == GT &&
         compareClockTime nftime srctime == GT &&
         compareClockTime iotime srctime == GT
        then fmap Just (readTypes opts mname)
        else return Nothing

-- Reads constructors, abstract call types, and input/output types
-- for a given module.
readTypes :: TermDomain a => Options -> String
          -> IO ([[(QName,Int)]], [(QName,ACallType a)],
                 [(QName,NonFailCond)], [(QName,InOutType a)])
readTypes opts mname = do
  csfile <- getConsTypesFile   opts mname
  ctfile <- getCallTypesFile   opts mname
  nffile <- getNonFailCondFile opts mname
  iofile <- getIOTypesFile     opts mname
  conss  <- readFile csfile >>= return . read
  cts    <- readFile ctfile >>= return . map read . lines
  nfcs   <- readFile nffile >>= return . map read . lines
  iots   <- readFile iofile >>= return . map read . lines
  return (conss,
          map (\ (fn,ct)  -> ((mname,fn), ct)) cts,
          map (\ (fn,nfc) -> ((mname,fn), nfc)) nfcs,
          map (\ (fn,iot) -> ((mname,fn), IOT iot)) iots)

--- Reads constructors, call types, non-fail conditions, and input/output types
--- for a given list of modules.
--- If some of the data files does not exist or is not newer
--- than the module source, the operation provided as the second argument
--- is applied before reading the files.
readTypesOfModules :: TermDomain a => Options
  -> (Options -> String -> IO ()) -> [String]
  -> IO ([[(QName,Int)]], [(QName, ACallType a)],
         [(QName,NonFailCond)], [(QName, InOutType a)])
readTypesOfModules opts computetypes mnames = do
  (xs,ys,zs, ws) <- mapM tryRead mnames >>= return . unzip4
  return (concat xs, concat ys, concat zs, concat ws)
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

--- Transforms a list of triples into a triple of lists.
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
          cts <- readFile fname >>= return . map read . lines
          return $ Just (map (\ (fn,ct) -> ((mname,fn), ct)) cts)
        else return Nothing
    else return Nothing

--- Reads the possibly previously inferred non-fail conditions for a
--- given module if it is up-to-date (where the modification time
--- of the module is passed as the second argument).
readNonFailCondFile :: Options -> ClockTime -> String
                    -> IO [(QName,NonFailCond)]
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
          cts <- readFile fname >>= return . map read . lines
          return $ map (\ (fn,ct) -> ((mname,fn), ct)) cts
        else return []
    else return []

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
writeSpecModule :: TermDomain a => Options -> String -> [FuncDecl]
                -> [(QName,ACallType a)] -> [(QName,NonFailCond)] -> IO ()
writeSpecModule opts mname fdecls pubntcalltypes funconds = do
  let ctmname = callTypesModule mname
      ctfile  = ctmname ++ ".curry"
  exct <- doesFileExist ctfile
  if null pubntcalltypes
    then when exct $ removeFile ctfile
    else do
      oldctmod <- if exct then readCompleteFile ctfile else return ""
      let ctmod = callTypeCond2SpecMod mname fdecls pubntcalltypes funconds
      unless (oldctmod == ctmod || not (optSpecModule opts)) $ do
        writeFile ctfile ctmod
        --includepath <- fmap (</> "include") getPackagePath
        printWhenStatus opts $
          "A Curry module '" ++ ctmname ++ "' with required call types\n" ++
          "and non-fail conditions is written to: '" ++ ctfile ++ "'.\n" -- ++
          --"To use it for future verifications, store this module\n" ++
          --"- either under '" ++ includepath ++ "'\n" ++
          --"- or in the source directory of module '" ++ mname ++ "'\n"

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

