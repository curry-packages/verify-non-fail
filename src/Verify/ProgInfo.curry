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
import Data.List          ( (\\), find )

import qualified Data.Map as Map
import FlatCurry.Build    ( fcFailed, pre )
import FlatCurry.FilesRW  ( readFlatCurry )
import FlatCurry.Goodies
import FlatCurry.Names    ( anonCons )
import FlatCurry.Types
import RW.Base

import Verify.Helpers     ( fst3, trd3 )

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
completeBranchesInFunc :: [(QName,ConsInfo)] -> Bool -> FuncDecl -> FuncDecl
completeBranchesInFunc consinfos withanon = updFuncBody (updCases completeCase)
 where
  completeCase ct e brs = Case ct e $ case brs of
    []                           -> []
    Branch (LPattern _) _   : _  -> brs
    Branch (Pattern pc _) _ : bs -> brs ++
      let otherqs  = map ((\p -> (patCons p, length (patArgs p)))
                                    . branchPattern) bs
          siblings = siblingsOfCons consinfos pc
      in if withanon
           then if null (siblings \\ otherqs)
                  then []
                  else [Branch (Pattern anonCons []) fcFailed]
           else -- since the patterns variables are irrelevant, we use 100,...:
                map (\(qc,ar) -> Branch (Pattern qc (take ar [100..])) fcFailed)
                    (siblings \\ otherqs)

------------------------------------------------------------------------------
--- The information about a constructor consists of the arity, type, and
--- the siblings of the constructor. The siblings are represented as
--- pairs of the qualified constructor name and their arity.
type ConsInfo = (Int, ConsType, [(QName,Int)])

--- The type of a constructor consists of the argument types, the
--- type constructor and the type parameters of the constructor.
data ConsType = ConsType [TypeExpr] QName [Int]
 deriving (Show, Read, Eq)

--- Transforms a list of type declarations into constructor information.
consInfoOfTypeDecls :: [TypeDecl] -> [(QName,ConsInfo)]
consInfoOfTypeDecls = concatMap consInfoOfTypeDecl

--- Transforms a type declaration into constructor information.
consInfoOfTypeDecl :: TypeDecl -> [(QName,ConsInfo)]
consInfoOfTypeDecl (TypeSyn _ _ _ _)                    = []
consInfoOfTypeDecl (TypeNew nt _ tvs (NewCons qc _ te)) =
  [(qc, (1, ConsType [te] nt (map fst tvs), []))]
consInfoOfTypeDecl (Type qt _ tvs cdecls) =
  map (\(Cons qc ar _ texps) ->
        (qc,
         (ar,
          ConsType texps qt (map fst tvs),
          --foldr FuncType (TCons qt (map (TVar . fst) tvs)) texps,
          filter ((/=qc) . fst) (map (\(Cons c car _ _) -> (c,car)) cdecls))))
      cdecls

--- Gets the the information about a given constructor name.
infoOfCons :: [(QName,ConsInfo)] -> QName -> ConsInfo
infoOfCons consinfos qc@(mn,cn) =
  maybe (error $ "No info for constructor '" ++ mn ++ "." ++ cn ++ "' found!")
        id
        (lookup qc consinfos)

--- Gets the arity of a constructor from information about all constructors.
arityOfCons :: [(QName,ConsInfo)] -> QName -> Int
arityOfCons consinfos qc@(mn,_)
  | null mn   = 0 -- literal
  | otherwise = fst3 (infoOfCons consinfos qc)

--- Gets the siblings of a constructor w.r.t. constructor information.
siblingsOfCons :: [(QName,ConsInfo)] -> QName -> [(QName,Int)]
siblingsOfCons consinfos qc = trd3 (infoOfCons consinfos qc)

--- Is a non-empty list of constructors complete, i.e., does it contain
--- all the constructors of a type?
--- The first argument contains information about all constructors in a program.
isCompleteConstructorList :: [(QName,ConsInfo)] -> [QName] -> Bool
isCompleteConstructorList _         []     = False
isCompleteConstructorList consinfos (c:cs)
  | null (fst c) = False -- literals are never complete
  | otherwise    = all (`elem` cs) (map fst (siblingsOfCons consinfos c))

-----------------------------------------------------------------------------
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
  , miCInfos  :: Map.Map String ConsInfo
  }

-- Generates a `ProgInfo` entry for a given FlatCurry program.
prog2ModInfo :: Prog -> ModInfo
prog2ModInfo prog =
  ModInfo prog 
          (Map.fromList (map (\fd -> (snd (funcName fd), funcType fd))
                             (progFuncs prog)))
          (Map.fromList (map (\(qc, cinfo) -> (snd qc, cinfo))
                             (consInfoOfTypeDecls (progTypes prog))))

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

--- Gets the type declaration for a given type constructor.
getTypeDeclOf :: IORef ProgInfo -> QName -> IO TypeDecl
getTypeDeclOf piref qtc@(mn,_) = do
  prog <- getFlatProgFor piref mn
  maybe (error $ "Type declaration for '" ++ show qtc ++ "' not found!")
        return
        (find (\td -> typeName td == qtc) (progTypes prog))

------------------------------------------------------------------------------
-- `ReadWrite` instance for `ConsType`.

instance ReadWrite ConsType where
  readRW strs r0 = (ConsType a' b' c',r3)
    where
      (a',r1) = readRW strs r0
      (b',r2) = readRW strs r1
      (c',r3) = readRW strs r2

  showRW params strs0 (ConsType a' b' c') = (strs3,show1 . (show2 . show3))
    where
      (strs1,show1) = showRW params strs0 a'
      (strs2,show2) = showRW params strs1 b'
      (strs3,show3) = showRW params strs2 c'

  writeRW params h (ConsType a' b' c') strs =
    (writeRW params h a' strs >>= writeRW params h b') >>= writeRW params h c'

  typeOf _ = monoRWType "ConsType"

------------------------------------------------------------------------------
