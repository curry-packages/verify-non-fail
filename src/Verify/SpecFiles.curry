------------------------------------------------------------------------------
--- Operations to write and read auxiliary files containing
--- verification information.
---
--- @author Michael Hanus
--- @version July 2023
-----------------------------------------------------------------------------

module Verify.SpecFiles where

import Control.Monad        ( when )
import Data.List

import AbstractCurry.Build
import AbstractCurry.Files
import AbstractCurry.Pretty ( showCProg )
import AbstractCurry.Select
import AbstractCurry.Types hiding ( pre )
import Contract.Names       ( decodeContractName, encodeContractName )
import Data.Time
import System.CurryPath     ( lookupModuleSourceInLoadPath, modNameToPath )
import System.Directory
import System.FilePath      ( (</>), dropFileName )

import PackageConfig        ( getPackagePath )
import Verify.CallTypes
import Verify.Helpers
import Verify.Options

------------------------------------------------------------------------------

-- The name of the Curry module where the call type specifications are stored.
callTypesModule :: String -> String
callTypesModule mname = mname ++ "_CALLTYPES"

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
      writeFile ctfile $
        showCProg (callTypes2SpecMod mname pubntcalltypes) ++ "\n"
      includepath <- fmap (</> "include") getPackagePath
      printWhenStatus opts $
        "A Curry module '" ++ ctmname ++
        "' with required call types is written to\n'" ++ ctfile ++ "'.\n" ++
        "To use it for future verifications, store it\n" ++
        "- either in the source directory of module '" ++ mname ++ "'\n" ++
        "- or under '" ++ includepath ++ "'"

--- Transforms call types to AbstractCurry module which can be read
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
