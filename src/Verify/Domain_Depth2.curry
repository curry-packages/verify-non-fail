------------------------------------------------------------------------------
--- The definition of the operations on the abstract domain
--- used for call types, in/out types, and verification of programs.
---
--- @author Michael Hanus
--- @version October 2023
------------------------------------------------------------------------------

module Verify.Domain
  ( valueAnalysis
  , AType, emptyType, anyType, aCons, aLit, litAsCons
  , consOfType, argTypesOfCons, joinAType, lubAType, showAType
  )
 where

import FlatCurry.Types

import Analysis.Types ( Analysis )
import qualified Analysis.TermDomain as TD
import Analysis.ValuesDepthK

------------------------------------------------------------------------------
--- The CASS analysis to approximate result values.
valueAnalysis :: Analysis AType
valueAnalysis = resultValueAnalysis2


--- The type of the abstract domain.
type AType = TD.DType2

--- Abstract representation of no possible value.
emptyType :: AType
emptyType = TD.emptyType

--- Abstract representation of the type of all values.
anyType :: AType
anyType = TD.anyType

--- Least upper bound of abstract values.
lubAType :: AType -> AType -> AType
lubAType = TD.lubType

--- Join two abstract values.
--- The result is `emptyType` if they are not compatible.
joinAType :: AType -> AType -> AType
joinAType = TD.joinType

--- The representation of a constructor application to a list of
--- abstract argument types.
aCons :: QName -> [AType] -> AType
aCons = TD.aCons

-- The representation of a literal in the abstract type domain.
aLit :: Literal -> AType
aLit = TD.aLit

--- The representation of a literal as a constructor.
litAsCons :: Literal -> QName
litAsCons = TD.litAsCons

--- The list of top-level constructors covered by an abstract type.
--- The list is empty for `anyType`.
consOfType :: AType -> [QName]
consOfType = TD.consOfType

--- The argument types of an abstract type (given as the last argument)
--- when it matches a given constructor/arity.
argTypesOfCons :: QName -> Int -> AType -> [AType]
argTypesOfCons = TD.argTypesOfCons

--- Shows an abstract value.
showAType :: AType -> String
showAType = TD.showType

------------------------------------------------------------------------------
