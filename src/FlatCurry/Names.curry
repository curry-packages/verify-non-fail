-----------------------------------------------------------------------------
--- Definition of some standard names in FlatCurry programs
--- together with their SMT names.
---
--- @author  Michael Hanus
--- @version December 2023
---------------------------------------------------------------------------

module FlatCurry.Names where

import FlatCurry.Types

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
unaryPrimOps =
  [("_impl#negate#Prelude.Num#Prelude.Int","-")
  ,("not","not")
  ]

--- Primitive binary operations of the prelude and their SMT names.
binaryPrimOps :: [(String,String)]
binaryPrimOps =
  [("constrEq","==")
  ,("_impl#==#Prelude.Eq#Prelude.Int","=")
  ,("_impl#==#Prelude.Eq#Prelude.Char","=")
  ,("/=","/=")  -- will be translated as negated '='
  ,("_impl#/=#Prelude.Eq#Prelude.Int","/=")
  ,("_impl#/=#Prelude.Eq#Prelude.Char","/=")
  ,("_impl#+#Prelude.Num#Prelude.Int","+")
  ,("_impl#-#Prelude.Num#Prelude.Int","-")
  ,("_impl#*#Prelude.Num#Prelude.Int","*")
  ,("_impl#negate#Prelude.Num#Prelude.Int","-")
  ,("_impl#div#Prelude.Integral#Prelude.Int","div")
  ,("_impl#mod#Prelude.Integral#Prelude.Int","mod")
  ,("_impl#rem#Prelude.Integral#Prelude.Int","rem")
  ,("_impl#>#Prelude.Ord#Prelude.Int",">")
  ,("_impl#<#Prelude.Ord#Prelude.Int","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Int",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Int","<=")
  ,("_impl#>#Prelude.Ord#Prelude.Float",">")
  ,("_impl#<#Prelude.Ord#Prelude.Float","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Float",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Float","<=")
  ,("_impl#>#Prelude.Ord#Prelude.Char",">")
  ,("_impl#<#Prelude.Ord#Prelude.Char","<")
  ,("_impl#>=#Prelude.Ord#Prelude.Char",">=")
  ,("_impl#<=#Prelude.Ord#Prelude.Char","<=")
  ]

----------------------------------------------------------------------------
