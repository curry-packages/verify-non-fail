------------------------------------------------------------------------------
-- Some auxiliary definitions used in different modules.
------------------------------------------------------------------------------

module Verify.Helpers where

import Data.Char          ( isDigit )
import Data.IORef
import Data.List

import Analysis.ProgInfo
import Analysis.Types
import CASS.Server        ( analyzeGeneric, analyzePublic )
import Data.Time          ( ClockTime )
import FlatCurry.Files    ( readFlatCurry )
import FlatCurry.Goodies
import FlatCurry.Types
import System.CurryPath   ( lookupModuleSourceInLoadPath )
import System.Directory   ( getModificationTime )

import FlatCurry.Build
import Verify.Options     ( Options, printWhenStatus )

------------------------------------------------------------------------------
-- Store for the analysis information of CASS. Used to avoid multiple reads.
data AnalysisStore a = AnaStore [(String, ProgInfo a)]

-- Loads CASS analysis results for a module and its imported entities.
loadAnalysisWithImports :: (Read a, Show a) =>
   IORef (AnalysisStore a) -> Analysis a -> Options -> Prog -> IO (QName -> a)
loadAnalysisWithImports anastore analysis opts prog = do
  maininfo <- getOrAnalyze (progName prog)
  impinfos <- mapM getOrAnalyze (progImports prog)
  return $ progInfo2Map $
    foldr combineProgInfo maininfo (map publicProgInfo impinfos)
 where
  getOrAnalyze mname = do
    AnaStore minfos <- readIORef anastore
    maybe (do printWhenStatus opts $ "Getting " ++ analysisName analysis ++
                " for '" ++ mname ++ "' via CASS..."
              minfo <- fmap (either id error) $ analyzeGeneric analysis mname
              writeIORef anastore (AnaStore ((mname,minfo) : minfos))
              return minfo)
          return
          (lookup mname minfos)

  -- Transform the analysis information from CASS into a mapping from
  -- names to analysis information.
  progInfo2Map :: ProgInfo a -> (QName -> a)
  progInfo2Map proginfo qf =
    maybe (error $ "Analysis information of '" ++ snd qf ++ "'' not found!")
          id
          (lookupProgInfo qf proginfo)

------------------------------------------------------------------------------
-- Sort a list function analysis results according to their names.
sortFunResults :: [(QName,a)] -> [(QName,a)]
sortFunResults = sortBy (\ct1 ct2 -> fst ct1 <= fst ct2)

-- Shows the analysis results of functions w.r.t. a formatting operation.
showFunResults :: (a -> String) -> [(QName,a)] -> [String]
showFunResults showf = map (\ (qf,r) -> snd qf ++ ": " ++ showf r)

------------------------------------------------------------------------------
--- Returns the modification time of a module.
getModuleModTime :: String -> IO ClockTime
getModuleModTime mname =
  lookupModuleSourceInLoadPath mname >>=
  maybe (error $ "Source file of module '" ++ mname ++ "' not found!")
        (\ (_,fn) -> getModificationTime fn)

------------------------------------------------------------------------------
--- Return the pattern variables of a pattern.
patternArgs :: Pattern -> [Int]
patternArgs (Pattern _ vs) = vs
patternArgs (LPattern _)   = []

--- Compute all constructors (and their arities) grouped by their types
--- from type declarations.
allConsOfTypes :: [TypeDecl] -> [[(QName,Int)]]
allConsOfTypes tdecls = filter (not . null) (map toConss tdecls)
 where
  toConss (Type    _ _ _ cdecls) = map (\ (Cons qc ar _ _) -> (qc,ar)) cdecls
  toConss (TypeSyn _ _ _ _)      = []
  toConss (TypeNew _ _ _ (NewCons qc _ _)) = [(qc,1)]

-- Reads a (possibly) qualified constructor string.
readQC :: String -> QName
readQC = readMQC []
 where
  readMQC ms s = let (s1,s2) = break (=='.') s
                 in case s2 of
                      ""  -> (toMod ms, s1) -- literal
                      [_] -> (toMod ms, "")
                      _:c:cs -> if isAlpha c && '.' `elem` cs
                                  then readMQC (ms ++ [s1]) (c:cs)
                                  else (toMod (ms ++ [s1]), c:cs)

  toMod = intercalate "."

--- The "unknown" type (hopefully not really used at the end).
unknownType :: TypeExpr
unknownType = TCons (pre "UNKNOWN") []

------------------------------------------------------------------------------
--- Returns the qualified names of all functions occurring in an expression.
funcsInExpr :: Expr -> [QName]
funcsInExpr e =
  trExpr (const id) (const id) comb lt fr (.) cas branch const e []
 where
  comb ct qn = foldr (.) (combtype ct qn)
  combtype ct qn = case ct of FuncCall       -> (qn:)
                              FuncPartCall _ -> (qn:)
                              _              -> id
  lt bs exp = exp . foldr (.) id (map (\ (_,ns) -> ns) bs)
  fr _ exp = exp
  cas _ exp bs = exp . foldr (.) id bs
  branch _ exp = exp

--- Transforms a list of argument variable (indices) and a function type
--- expression into a list of corresponding typed variables.
funcType2TypedVars :: [Int] -> TypeExpr -> [(Int,TypeExpr)]
funcType2TypedVars []     _     = []
funcType2TypedVars (v:vs) ftype = case ftype of
    FuncType t1 t2 -> (v,t1) : funcType2TypedVars vs t2
    ForallType _ t -> funcType2TypedVars (v:vs) t
    _              -> error "Illegal function type in funcType2TypedVars"

------------------------------------------------------------------------------
--- A position in a term is represented as list of integers.
type Pos = [Int]

--- Fresh variables, i.e., variables not occurring in a position of
--- the left-hand side, are represented as a root position.
freshVarPos :: Pos
freshVarPos = []

--- Is a variable position the position of a fresh variable, i.e.,
--- a variable which does not occur in the left-hand side?
isFreshVarPos :: Pos -> Bool
isFreshVarPos = null

------------------------------------------------------------------------------
--- Some predefined data constructors grouped by their types.
--- Used for testing in module CallTypes.
stdConstructors :: [[QName]]
stdConstructors =
  [ [pre "False", pre "True"]
  , [pre "[]", pre ":"]
  , [pre "Nothing", pre "Just"]
  , [pre "Left", pre "Right"]
  , [pre "LT", pre "EQ", pre "GT"]
  , [pre "IOError", pre "UserError", pre "FailError", pre "NondetError"]
  ] ++
  map (\n -> [pre $ "(" ++ take n (repeat ',') ++ ")"]) [0 .. 8]

--- Is this the name of a non-failing encapsulated search operation?
isEncSearchOp :: QName -> Bool
isEncSearchOp qf@(mn,_) =
  mn `elem` ["Control.Search.Unsafe", "Control.Search.AllValues"] ||
  qf `elem` map (\n -> ("Control.AllValues",n))
                ["allValues", "oneValue", "isFail"]

--- Is this the name of a set function?
isSetFunOp :: QName -> Bool
isSetFunOp (mn,fn) =
  (mn == "Control.Search.SetFunctions" || mn == "Control.SetFunctions") &&
  take 3 fn == "set" &&
  all isDigit (drop 3 fn)

-- Is a qualified name an allowed Curry identifier (i.e., not a generated id)?
isCurryID :: QName -> Bool
isCurryID (_,n) = case n of
  []               -> False
  c:cs | isAlpha c -> all (\c -> isAlphaNum c || c `elem` "'_") cs
       | otherwise -> all (flip elem opChars) n
 where
  opChars = "~!@#$%^&*+-=<>?./|\\:"

------------------------------------------------------------------------------
fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

snd3 :: (a,b,c) -> b
snd3 (_,y,_) = y

trd3 :: (a,b,c) -> c
trd3 (_,_,z) = z

------------------------------------------------------------------------------
