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

import qualified Data.Map as Map
import FlatCurry.Goodies
import FlatCurry.Types

import Verify.Helpers ( readTransFlatCurry )

------------------------------------------------------------------------------
--- The global program information is a mapping from module names
--- to infos about the module. The main program keeps an `IORef` to this
--- structure.
data ProgInfo = ProgInfo
  { progInfos :: [(String,ModInfo)] -- program infos of all modules
  }

emptyProgInfo :: ProgInfo
emptyProgInfo = ProgInfo []

-- The information for each module contains the program and maps
-- for function and constructor types.
data ModInfo = ModInfo
  { miProg   :: Prog
  , miFTypes :: Map.Map String TypeExpr
  , miCTypes :: Map.Map String TypeExpr
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
