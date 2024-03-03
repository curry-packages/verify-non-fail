-----------------------------------------------------------------------------
--- This module contains the definition and operations for a state
--- containing information about already loaded FlatCurry programs.
--- The state is used during the execution of the tool in order to
--- avoid multiple loading of FlatCurry programs.
---
--- @author  Michael Hanus
--- @version March 2024
---------------------------------------------------------------------------

module Verify.ProgInfo
 where

import Data.IORef
import Data.List          ( (\\) )

import qualified Data.Map as Map
import FlatCurry.Build    ( fcFailed, pre )
import FlatCurry.Files    ( readFlatCurry )
import FlatCurry.Goodies
import FlatCurry.Names    ( anonCons )
import FlatCurry.Types

import Verify.Helpers     ( allConsOfTypes, getSiblingsOf )

------------------------------------------------------------------------------
--- Read and transform a module in FlatCurry format.
--- In particular, occurrences of `Prelude.?` are transformed into
--- `Or` expressions and top-level `Forall` quantifiers are removed in
--- function signatures.
readTransFlatCurry :: String -> IO Prog
readTransFlatCurry mname = do
  readFlatCurry mname >>= return . transformChoiceInProg . removeTopForallType

--- Replace all occurrences of `Prelude.?` in a FlatCurry program by
--- `Or` expressions.
transformChoiceInProg :: Prog -> Prog
transformChoiceInProg = updProgExps (updCombs replaceChoiceCall)
 where
  replaceChoiceCall ct qf es =
    if ct == FuncCall && qf == pre "?" && length es == 2
      then Or (es!!0) (es!!1)
      else Comb ct qf es

--- Remove the top-level `ForallType` constructors from all function signatures.
removeTopForallType :: Prog -> Prog
removeTopForallType = updProgFuncs (map rmForallTypeInFunc)
 where
  rmForallTypeInFunc = updFunc id id id rmForallType id

  rmForallType texp = case texp of ForallType _ te -> te
                                   _               -> texp

--- Complete all partial case branches occurring in the body of a function
--- by adding `Prelude.failed` branches. The first argument contains all data
--- constructors grouped by their data type. If the second argument is `True`,
--- only a single branch with an anonymous pattern is added (if necessary),
--- otherwise branches for all missing patterns are added.
completeBranchesInFunc :: [[(QName,Int)]] -> Bool -> FuncDecl -> FuncDecl
completeBranchesInFunc allcons withanon = updFuncBody (updCases completeCase)
 where
  completeCase ct e brs = Case ct e $ case brs of
    []                           -> []
    Branch (LPattern _) _   : _  -> brs
    Branch (Pattern pc _) _ : bs -> brs ++
      let otherqs  = map ((\p -> (patCons p, length (patArgs p)))
                                    . branchPattern) bs
          siblings = maybe (error $ "Siblings of " ++ snd pc ++ " not found!")
                           id
                           (getSiblingsOf allcons pc)
      in if withanon
           then if null (siblings \\ otherqs)
                  then []
                  else [Branch (Pattern anonCons []) fcFailed]
           else -- since the patterns variables are irrelevant, we use 100,...:
                map (\(qc,ar) -> Branch (Pattern qc (take ar [100..])) fcFailed)
                    (siblings \\ otherqs)

------------------------------------------------------------------------------
--- The global program information is a mapping from module names
--- to infos about the module. The main program keeps an `IORef` to this
--- structure.
data ProgInfo = ProgInfo
  { progInfos :: [(String,ModInfo)] -- program infos of all modules
  }

emptyProgInfo :: ProgInfo
emptyProgInfo = ProgInfo []

-- The information for each module contains the program, maps
-- for function and constructor types, and all constructors (and their arities)
-- declared in the module grouped by their types
data ModInfo = ModInfo
  { miProg    :: Prog
  , miFTypes  :: Map.Map String TypeExpr
  , miCTypes  :: Map.Map String TypeExpr
  }

-- Generates a `ProgInfo` entry for a given FlatCurry program.
prog2ModInfo :: Prog -> ModInfo
prog2ModInfo prog =
  ModInfo prog (Map.fromList (map fun2sig (progFuncs prog)))
               (Map.fromList (concatMap type2ctypes (progTypes prog)))
 where
  fun2sig fd = (snd (funcName fd), funcType fd)

  type2ctypes (TypeSyn _ _ _ _)                    = []
  type2ctypes (TypeNew nt _ tvs (NewCons qc _ te)) =
    [(snd qc, FuncType te (TCons nt (map (TVar . fst) tvs)))]
  type2ctypes (Type qt _ tvs cdecls) =
    map (\(Cons qc _ _ texps) ->
             (snd qc, foldr FuncType (TCons qt (map (TVar . fst) tvs)) texps))
        cdecls

------------------------------------------------------------------------------
-- Access operations

--- Read a module and adds the info for it.
addModInfoFor :: IORef ProgInfo -> String -> IO ()
addModInfoFor piref mname = do
  prog <- readTransFlatCurry mname
  pis <- readIORef piref
  writeIORef piref
    (pis { progInfos = (progName prog, prog2ModInfo prog) : progInfos pis})

--- Does the info for a module with a given name already exists?
hasModInfoFor :: IORef ProgInfo -> String -> IO Bool
hasModInfoFor piref mn = do
  pi <- readIORef piref
  return $ maybe False (const True) (lookup mn (progInfos pi))

--- Gets the info for a module with a given name.
--- If it is not already stored, read the module and store it.
getModInfoFor :: IORef ProgInfo -> String -> IO ModInfo
getModInfoFor piref mname = do
  pi <- readIORef piref
  maybe (addModInfoFor piref mname >> getModInfoFor piref mname)
        return
        (lookup mname (progInfos pi))

--- Gets the FlatCurry program for a module with a given name.
getFlatProgFor :: IORef ProgInfo -> String -> IO Prog
getFlatProgFor piref mn = fmap miProg $ getModInfoFor piref mn

------------------------------------------------------------------------------
