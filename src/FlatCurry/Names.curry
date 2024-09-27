-----------------------------------------------------------------------------
--- Definition of some standard names in FlatCurry programs used in this tool
--- together with their SMT names.
---
--- @author  Michael Hanus
--- @version September 2024
---------------------------------------------------------------------------

module FlatCurry.Names where

import FlatCurry.Build ( pre )
import FlatCurry.Types
import qualified FlatCurry.Names2SMT

----------------------------------------------------------------------------
--- An "anonymous" constructor is used to represent case expressions
--- with a final "catch all" alternative.
anonCons :: QName
anonCons = pre "_"

----------------------------------------------------------------------------
--- Is a qualified FlatCurry name primitive?
isPrimOp :: QName -> Bool
isPrimOp (mn,fn) = mn=="Prelude" && fn `elem` map fst preludePrimOps

--- Primitive operations of the prelude and their SMT names.
preludePrimOps :: [(String,String)]
preludePrimOps = unaryPrimOps ++ binaryPrimOps ++
  [("otherwise","True")
  ,("apply","apply") -- TODO...
  ]

--- Primitive unary operations of the prelude and their SMT names.
unaryPrimOps :: [(String,String)]
unaryPrimOps = FlatCurry.Names2SMT.unaryPrimOps

--- Primitive binary operations of the prelude and their SMT names.
binaryPrimOps :: [(String,String)]
binaryPrimOps = map transEqu2 (drop 2 FlatCurry.Names2SMT.binaryPrimOps)
 where
  transEqu2 (fc,fsmt) = (fc, if fsmt == "=" then "==" else fsmt)

----------------------------------------------------------------------------
