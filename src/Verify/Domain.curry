------------------------------------------------------------------------------
--- The definition of the operations on the abstract domain
--- used for call types, in/out types, and verification of programs.
---
--- @author Michael Hanus
--- @version October 2023
------------------------------------------------------------------------------

module Verify.Domain
  ( domainName
  , AType, emptyType, anyType, anyTypes, aCons, aLit, litAsCons
  , joinAType, lubAType, showAType
  , analyzeResultValues )
 where

import Data.IORef

import FlatCurry.Types

import qualified Analysis.Values as AV

import Verify.Helpers
import Verify.Options

------------------------------------------------------------------------------
--- A unique name for the abstract domain.
--- Used for the cache to distinguish information computed with different
--- domains.
domainName :: String
domainName = "TopCons"

--- The type of the abstract domain.
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
aCons qc _ = AV.aCons qc

-- The representation of a literal in the abstract type domain.
aLit :: Literal -> AType
aLit l = aCons (AV.lit2cons l) []

--- The representation of a literal as a constructor.
litAsCons :: Literal -> QName
litAsCons = AV.lit2cons

--- Shows an abstract value.
showAType :: AType -> String
showAType = AV.showAType

--- Loads analysis information about abstract result values from CASS.
analyzeResultValues :: IORef (AnalysisStore AType) -> Options -> Prog
                    -> IO (QName -> AType)
analyzeResultValues astore opts prog =
  loadAnalysisWithImports astore AV.resultValueAnalysis opts prog

------------------------------------------------------------------------------
