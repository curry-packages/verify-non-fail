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
  , consOfType, argTypesOfCons, joinAType, lubAType, showAType
  , analyzeResultValues )
 where

import Data.IORef

import FlatCurry.Types

import qualified Analysis.ValuesK as AV

import Verify.Helpers
import Verify.Options

------------------------------------------------------------------------------
--- The depth used in the domain.
--- Note that a corresponding analysis with this depth must be registered
--- in CASS. These are current for depth 1, 2, or 5.
depthK :: Int
depthK = 5

------------------------------------------------------------------------------
--- A unique name for the abstract domain.
--- Used for the cache to distinguish information computed with different
--- domains.
domainName :: String
domainName = "Depth" ++ show depthK

--- The type of the abstract domain.
type AType = AV.DType

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
lubAType = AV.lubDType

--- Join two abstract values.
--- The result is `emptyType` if they are not compatible.
joinAType :: AType -> AType -> AType
joinAType = AV.joinDType

--- The representation of a constructor application to a list of
--- abstract argument types.
aCons :: QName -> [AType] -> AType
aCons = AV.aCons depthK

-- The representation of a literal in the abstract type domain.
aLit :: Literal -> AType
aLit l = aCons (litAsCons l) []

--- The representation of a literal as a constructor.
litAsCons :: Literal -> QName
litAsCons = AV.litAsCons

--- The list of top-level constructors covered by an abstract type.
--- The list is empty for `anyType`.
consOfType :: AType -> [QName]
consOfType = AV.consOfType

--- The argument types of an abstract type (given as the last argument)
--- when it matches a given constructor/arity.
argTypesOfCons :: QName -> Int -> AType -> [AType]
argTypesOfCons = AV.argTypesOfCons

--- Shows an abstract value.
showAType :: AType -> String
showAType = AV.showDType

--- Loads analysis information about abstract result values from CASS.
analyzeResultValues :: IORef (AnalysisStore AType) -> Options -> Prog
                    -> IO (QName -> AType)
analyzeResultValues astore opts prog =
  loadAnalysisWithImports astore (AV.valueKAnalysis depthK) opts prog

------------------------------------------------------------------------------
