------------------------------------------------------------------------------
--- Operations to write and read auxiliary files containing
--- verification information.
---
--- @author Michael Hanus
--- @version July 2023
-----------------------------------------------------------------------------

module Verify.Files where

import Control.Monad     ( unless, when )
import Data.List

import Data.Time
import FlatCurry.Types
import System.Directory
import System.FilePath   ( (</>) )

import PackageConfig     ( getPackagePath )
import Verify.CallTypes
import Verify.Helpers
import Verify.IOTypes
import Verify.Options
import Verify.SpecFiles

------------------------------------------------------------------------------
-- The name of the file containing required call types for a module.
pubCallTypesFile :: String -> String
pubCallTypesFile mname = mname ++ "-CALLTYPES"

-- The name of the file containing all call types of a module.
callTypesFile :: String -> String
callTypesFile mname = verifyDataDir </> mname ++ "-CALLTYPES"

-- The name of the file containing all input/output types of a module.
ioTypesFile :: String -> String
ioTypesFile mname = verifyDataDir </> mname ++ "-IOTYPES"

-- The name of the file containing all constructor of a module.
consTypesFile :: String -> String
consTypesFile mname = verifyDataDir </> mname ++ "-CONSTYPES"

-- Stores non-trivial call types and non-trivial input/output types.
storeTypes :: Options -> String -> [TypeDecl]
           -> [(QName,[[CallType]])] -- public non-trivial call types
           -> [(QName,[[CallType]])] -- all call types
           -> [(QName,InOutType)]    -- all input output types
           -> IO ()
storeTypes opts mname tdecls pubntcalltypes calltypes iotypes = do
  createDirectoryIfMissing True verifyDataDir
  writeFile (callTypesFile mname)
    (unlines (map (\ ((_,fn),ct) -> show (fn,ct)) (filterMod calltypes)))
  writeFile (ioTypesFile mname)
    (unlines (map (\ ((_,fn), IOT iots) -> show (fn,iots)) (filterMod iotypes)))
  writeFile (consTypesFile mname) (show (allConsOfTypes tdecls))
  let sortedpubntcalltypes = sortCTs pubntcalltypes
  writeCallTypeSpecMod opts mname sortedpubntcalltypes
 where
  filterMod xs = filter (\ ((mn,_),_) -> mn == mname) xs

  sortCTs = sortBy (\ct1 ct2 -> fst ct1 <= fst ct2)

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
{-  NO LONGER USED:
-- Writing and reading public call type file for a module.

--- Writes a file containing the non-trivial call types for a given module.
writeModuleCallTypeFile :: Options -> String -> [(QName,[[CallType]])] -> IO ()
writeModuleCallTypeFile opts mname pubntcalltypes = do
  let ctfile = pubCallTypesFile mname
  exct <- doesFileExist ctfile
  when exct $ renameFile ctfile (ctfile ++ ".BAK")
  writeFile ctfile (showCallTypes pubntcalltypes)
  printWhenStatus opts $
    "File '" ++ ctfile ++ "' with required call types written"
  when exct $ printWhenStatus opts $
    "(old file renamed to '" ++ ctfile ++ ".BAK')"

--- Shows a call types in a better programmer-readable way.
showCallTypes :: [(QName,[[CallType]])] -> String
showCallTypes =
  unlines . map (\ ((_,fn),cts) -> show (fn, map (map ct2mb) cts))
 where
  ct2mb AnyT          = Nothing
  ct2mb (MCons cscts) = Just $ map cs2mb cscts

  cs2mb ct@((mn,mc),cts) =
    if any (/= AnyT) cts
      then error $ "Call type with nested constructors: " ++ show ct
      else ((if null mn then "" else mn ++ ".") ++ mc, length cts)


--- Reads the public non-trivial call types (which have been already
--- computed or explicitly specified) for a given module.
--- If the file does not exist, try to read a file from the `include`
--- directory (for standard libraries).
readPublicCallTypeFile :: Options -> String -> IO [(QName,[[CallType]])]
readPublicCallTypeFile opts mname = do
  let fname = pubCallTypesFile mname
  existsf <- doesFileExist fname
  if existsf
    then do
      printWhenStatus opts $
        "Reading required call types from '" ++ fname ++ "'..."
      cts <- readFile fname >>= return . readCallTypes
      return (map (\ (fn,ct) -> ((mname,fn), ct)) cts)
    else readInclude
 where
  readInclude = do
    pkgpath <- getPackagePath
    let ifname = pkgpath </> "include" </> mname ++ "-CALLTYPES"
    existsif <- doesFileExist ifname
    if existsif
      then do
        printWhenStatus opts $
          "Reading required call types from '" ++ ifname ++ "'..."
        cts <- readFile ifname >>= return . readCallTypes
        return (map (\ (fn,ct) -> ((mname,fn), ct)) cts)
      else return []


--- Reads a list of call types produced by 'showCallTypes'.
readCallTypes :: String -> [(String,[[CallType]])]
readCallTypes =
  map (\ (fn,cts) -> (fn, map (map mb2ct) cts)) . map read . lines
 where
  mb2ct Nothing       = AnyT
  mb2ct (Just cscts)  = MCons $ map mb2cs cscts
   where
    mb2cs (qf, ar) = (readQC qf, take ar (repeat AnyT))

------------------------------------------------------------------------------
-}
