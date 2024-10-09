------------------------------------------------------------------------------
--- Auxiliaries for printing FlatCurry entities.
---
--- @author Michael Hanus
--- @version January 2024
------------------------------------------------------------------------------

module FlatCurry.Print
 where

import FlatCurry.Goodies
import FlatCurry.Pretty as FCP
import FlatCurry.Types
import Text.Pretty                ( Doc, (<+>), align, pPrint, text )

--- Shows a pretty-printed FlatCurry program.
showFlatProg :: Prog -> String
showFlatProg = pPrint . ppProg defaultOptions { qualMode = QualNone}

--- Shows a pretty-printed FlatCurry expression.
showTypeExp :: TypeExpr -> String
showTypeExp = pPrint . ppTypeExp

--- Pretty prints a FlatCurry expression.
ppTypeExp :: TypeExpr -> Doc
ppTypeExp = FCP.ppTypeExp defaultOptions { qualMode = QualNone}

--- Shows a pretty-printed variable binding to a FlatCurry expression.
showBindExp :: Int -> Expr -> String
showBindExp bv e = pPrint $ text ('v' : show bv ++ " |-> ") <+> align (ppExp e)

--- Shows a pretty-printed FlatCurry expression.
showExp :: Expr -> String
showExp = pPrint . ppExp

--- Pretty prints a FlatCurry expression.
ppExp :: Expr -> Doc
ppExp = FCP.ppExp defaultOptions { qualMode = QualNone}

--- Pretty prints a FlatCurry function.
showFuncDecl :: FuncDecl -> String
showFuncDecl =
  pPrint . ppFuncDecl defaultOptions { qualMode = QualNone}

--- Pretty prints a FlatCurry function as a lambda expression.
showFuncDeclAsLambda :: FuncDecl -> String
showFuncDeclAsLambda fdecl =
  let rule = funcRule fdecl
  in '\\' : unwords (map (\i -> 'v' : show i) (ruleArgs rule)) ++
     " -> " ++ showExp (ruleBody rule)

------------------------------------------------------------------------------
