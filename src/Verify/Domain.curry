------------------------------------------------------------------------------
--- The definition of the operations on the abstract domain
--- used for call types, in/out types, and verification of programs.
---
--- @author Michael Hanus
--- @version October 2023
------------------------------------------------------------------------------

module Verify.Domain
  ( AType, emptyType, anyType, anyTypes, aCons, aLit, litAsCons
  , joinAType, lubAType, showAType
  , AnalysisStore(..), analyzeResultValues )
 where

import Data.IORef

import Analysis.ProgInfo
import Analysis.Types
import CASS.Server         ( analyzeGeneric, analyzePublic )
import FlatCurry.Goodies
import FlatCurry.Types

import qualified Analysis.Values as AV

import Verify.Options

type AType = AV.AType

--- Abstract representation of no possible value.
emptyType :: AType
emptyType = AV.emptyType

--- Abstract representation of the type of all values.
anyType :: AType
anyType = AV.anyType

--- A list of any types of a given length.
anyTypes :: Int -> [AType]
anyTypes n = take n (repeat anyType)

--- Least upper bound of abstract values.
lubAType :: AType -> AType -> AType
lubAType = AV.lubAType

--- Join two abstract values.
--- The result is `emptyType` if they are not compatible.
joinAType :: AType -> AType -> AType
joinAType = AV.joinAType

--- The representation of a constructor application to a list of
--- abstract argument types.
aCons :: QName -> [AType] -> AType
aCons qc atypes =
  if all (== anyType) atypes
    then AV.aCons qc --TODO: generalize for other domains
    else emptyType

-- The representation of a literal in the abstract type domain.
aLit :: Literal -> AType
aLit l = aCons (AV.lit2cons l) []

--- The representation of a literal as a constructor.
litAsCons :: Literal -> QName
litAsCons = AV.lit2cons

--- Shows an abstract value.
showAType :: AType -> String
showAType = AV.showAType

------------------------------------------------------------------------------
-- Operations to process and read result value approximations via CASS

-- Store for the analysis information of CASS. Used to avoid multiple reads.
data AnalysisStore a = AnaStore [(String, ProgInfo a)]

analyzeResultValues :: IORef (AnalysisStore AType) -> Options -> Prog
                    -> IO (QName -> AType)
analyzeResultValues astore opts prog = do
  rvinfo <- loadAnalysisWithImports astore AV.resultValueAnalysis opts prog
  return (cass2AType rvinfo)

-- Loads CASS analysis results for a module and its imported entities.
loadAnalysisWithImports :: (Read a, Show a) =>
   IORef (AnalysisStore a) -> Analysis a -> Options -> Prog -> IO (ProgInfo a)
loadAnalysisWithImports anastore analysis opts prog = do
  maininfo <- getOrAnalyze (progName prog)
  impinfos <- mapM getOrAnalyze (progImports prog)
  return $ foldr combineProgInfo maininfo (map publicProgInfo impinfos)
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

-- Transform the result value information from CASS into a mapping w.r.t.
-- local `AType` values.
cass2AType :: ProgInfo AType -> (QName -> AType)
cass2AType resvalinfo qf =
  maybe (error $ "Result values information of " ++ snd qf ++ " not found!")
        id
        (lookupProgInfo qf resvalinfo)

------------------------------------------------------------------------------
