------------------------------------------------------------------------------
--- The definition of the operations on the abstract domain
--- used for call types, in/out types, and verification of programs.
---
--- @author Michael Hanus
--- @version October 2023
------------------------------------------------------------------------------

module Verify.Domain
  ( AType, emptyType, anyType, anyTypes, aCons, aLit, litAsCons
  , joinAType, lubAType, showAType )
 where

import FlatCurry.Types ( Literal, QName )

import qualified Analysis.Values as AV

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