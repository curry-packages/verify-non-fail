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
import FlatCurry.Goodies
import FlatCurry.Types
import System.CurryPath   ( lookupModuleSourceInLoadPath )
import System.Directory   ( getModificationTime )

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
--- Replace all occurrences of `Prelude.?` in a FlatCurry program by
--- `Or` expressions.
transformChoiceInProg :: Prog -> Prog
transformChoiceInProg = updProg id id id (map transChoiceInFunc) id
 where
  transChoiceInFunc = updFunc id id id id transChoiceInRule

  transChoiceInRule = updRule id transChoiceInExpr id

  transChoiceInExpr = updCombs updChoiceComb
   where
    updChoiceComb ct qf es =
      if ct == FuncCall && qf == pre "?" && length es == 2
        then Or (es!!0) (es!!1)
        else Comb ct qf es

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
--- Transform name into Prelude-qualified name.
pre :: String -> QName
pre f = ("Prelude",f)

--- Gets the siblings of a constructor w.r.t. all constructors grouped by types.
getSiblingsOf :: [[(QName,Int)]] -> QName -> Maybe [(QName,Int)]
getSiblingsOf allcons qc =
  maybe Nothing
        (\qcs -> Just $ deleteBy (\x y -> fst x == fst y) (qc,0) qcs)
        (find ((qc `elem`) . map fst) allcons)

--- Gets the siblings of a constructor w.r.t. all constructors grouped by types.
arityOfCons :: [[(QName,Int)]] -> QName -> Int
arityOfCons allcons qc@(mn,cn)
  | null mn -- literal?
  = 0
  | otherwise
  = maybe (error $ "Arity of constructor '" ++ mn ++ "." ++ cn ++ "' not found")
          id
          (lookup qc (concat allcons))

--- Is a non-empty list of constructors complete, i.e., does it contain
--- all the constructors of a type?
--- The first argument contains all the constructors in a program.
isCompleteConstructorList :: [[(QName,Int)]] -> [QName] -> Bool
isCompleteConstructorList _       []     = False
isCompleteConstructorList allcons (c:cs) =
  maybe False
        (\siblings -> all (`elem` cs) (map fst siblings))
        (getSiblingsOf allcons c)

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
isEncSearchOp qf =
  qf `elem` map (\n -> ("Control.AllValues",n))
                ["allValues", "oneValue", "isFail"]

--- Is this the name of a set function?
isSetFunOp :: QName -> Bool
isSetFunOp (mn,fn) =
  mn == "Control.SetFunctions" && take 3 fn == "set" &&
  all isDigit (drop 3 fn)

------------------------------------------------------------------------------
