------------------------------------------------------------------------------
--- The definition of the operations on the abstract domain
--- used for call types, in/out types, and verification of programs.
---
--- @author Michael Hanus
--- @version October 2023
------------------------------------------------------------------------------

module Verify.Domain
  ( valueAnalysis
  , AType, emptyType, isEmptyType, anyType, isAnyType, aCons, aLit, litAsCons
  , consOfType, argTypesOfCons, joinType, lubType, showType
  )
 where

import FlatCurry.Types

import Analysis.Types ( Analysis )
import qualified Analysis.TermDomain as TD
import Analysis.Values

------------------------------------------------------------------------------
--- The CASS analysis to approximate result values.
valueAnalysis :: Analysis AType
valueAnalysis = resultValueAnalysisTop


--- The type of the abstract domain.
type AType = TD.AType

--- Abstract representation of no possible value.
emptyType :: AType
emptyType = TD.emptyType

--- Does an abstract type represent no value?
isEmptyType :: AType -> Bool
isEmptyType = TD.isEmptyType

--- Abstract representation of the type of all values.
anyType :: AType
anyType = TD.anyType

--- Does an abstract type represent any value?
isAnyType :: AType -> Bool
isAnyType = TD.isAnyType

--- Least upper bound of abstract values.
lubType :: AType -> AType -> AType
lubType = TD.lubType

--- Join two abstract values.
--- The result is `emptyType` if they are not compatible.
joinType :: AType -> AType -> AType
joinType = TD.joinType

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
--- For the top constructor domain, the arguments have always any type.
argTypesOfCons :: QName -> Int -> AType -> [AType]
argTypesOfCons = TD.argTypesOfCons

--- Shows an abstract value.
showType :: AType -> String
showType = TD.showType

------------------------------------------------------------------------------
