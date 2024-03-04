------------------------------------------------------------------------------
--- This module provides an abstract representation of a variant
--- of the SMT-LIB language appropriate for checking Curry programs.
--- In particular, polymorphic function declarations are supported.
---
--- It might be later replaced by an extended version of the
--- SMT-LIB language specified in the package `smtlib`.
---
--- @author  Michael Hanus
--- @version February 2024
------------------------------------------------------------------------------

module Verify.ESMT where

import Data.List ( (\\), intercalate, isPrefixOf, union )

import qualified Data.Map as FM
import Text.Pretty

------------------------------------------------------------------------------
--- An SMT-LIB script consists of a list of commands.
data SMTLib = SMTLib [Command]
  deriving (Eq, Show)

type SVar  = Int    -- variables 
type Ident = String -- identifiers (e.g., functions)


--- Sorts

data Sort = SComb Ident [Sort]
  deriving (Eq, Show)

-- Shows a sort as a string.
showSort :: Sort -> String
showSort (SComb s ss) = s ++ intercalate "_" (map showSort ss)

--- Does the sort represent a type parameter (`TVar i`)?
isTypeParameter :: Sort -> Bool
isTypeParameter (SComb s ss) = null ss && "TVar" `isPrefixOf` s && length s > 4

--- A sort represent an anonymous type (`SComb "_" []`).
anonymousType :: Sort
anonymousType = SComb "_" []

--- Does the sort represent an anonymous type (`SComb "_" []`)?
isAnonymousType :: Sort -> Bool
isAnonymousType (SComb s ss) = null ss && s == "_"

----------------------------------------------------------------------------
--- Terms

--- A literal is a natural number, float, or string.
data TLiteral = TInt    Int
              | TFloat  Float
              | TString String
 deriving (Eq, Show)

--- An identifier possibly with a sort attached.
data QIdent = Id Ident
            | As Ident Sort
 deriving (Eq, Show)

--- The identifier of a possibly sorted identifier.
qidName :: QIdent -> Ident
qidName (Id n  ) = n
qidName (As n _) = n

--- Sorted variables used in quantifiers.
data SortedVar = SV SVar Sort
 deriving (Eq, Show)

data Pattern = PComb QIdent [SVar]
 deriving (Eq, Show)

--- Terms occurring in formulas
data Term = TConst TLiteral
          | TSVar  SVar
          | TComb  QIdent [Term]
          | Let    [(SVar, Term)] Term
          | Forall [SortedVar] Term
          | Exists [SortedVar] Term
          | Match  Term [(Pattern, Term)]
          --| Annot  Term [Attribute]
 deriving (Eq, Show)

-- Smart constructors:

-- `True` pattern:
pTrue :: Pattern
pTrue = PComb (Id "true") []

-- `False` pattern:
pFalse :: Pattern
pFalse = PComb (Id "false") []

--- Combined term with string identifier.
tComb :: Ident -> [Term] -> Term
tComb f ts = TComb (Id f) ts

--- Conjunction
tConj :: [Term] -> Term
tConj = tComb "and"

--- Disjunction
tDisj :: [Term] -> Term
tDisj = tComb "or"

--- Negation
tNot :: Term -> Term
tNot t = tComb "not" [t]

--- A Boolean true.
tTrue :: Term
tTrue = tComb "true" []

--- A Boolean false.
tFalse :: Term
tFalse = tComb "false" []

--- Equality between two terms.
tEqu :: Term -> Term -> Term
tEqu t1 t2 = tComb "=" [t1, t2]

--- Equality between a variable and a term.
tEquVar :: SVar -> Term -> Term
tEquVar v t = tEqu (TSVar v) t

--- if-then-else expression
tITE :: Term -> Term -> Term -> Term
tITE b t f = tComb "ite" [b,t,f]

--- Let expression.
tLet :: [(SVar, Term)] -> Term -> Term
tLet = Let

--- A constant with a sort declaration.
sortedConst :: Ident -> Sort -> Term
sortedConst c s = TComb (As c s) []

----------------------------------------------------------------------------
--- Datatype declaration consisting of type variables and constructor decls.
data DTDecl = DT [Ident] [DTCons] -- polymorphic type
 deriving (Eq, Show)

data DTCons = DCons Ident [(Ident,Sort)]
 deriving (Eq, Show)

--- The signature of a function declaration.
data FunSig = FunSig Ident [Sort] Sort
  deriving (Eq, Show)

--- The signature and arguments of a function declaration.
data FunDec = FunDec Ident [SortedVar] Sort
  deriving (Eq, Show)

--- A definition of a polymorphic, possibly non-deterministic, operation.
--- The first component is a list of type paramters
--- which can be used in the type signature and the term.
--- The term in the third argument is the axiomatization of the function
--- definition. Thus, it contains all quantifiers and the equation
--- `(= (f x1...xn) rhs-term)` so that it can also be used to specify,
--- by exploiting disjunctions, the meaning of non-deterministic operations.
type FunSigTerm = ([Ident], FunSig, Term)

--- Commands in SMT script.
--- The command `DefineSigsRec` is new. It is similar to `DefineFunsRec`,
--- but the associated term is the axiomatization of the function
--- definition. Thus, it contains all quantifiers and the equation
--- `(= (f x1...xn) rhs-term)` so that it can also be used to specify,
--- by exploiting disjunctions, the meaning of non-deterministic functions.
--- Moreover, it supports parametric polymoprhism by providing a list
--- of type paramters which can be used in the type signature and term.
--- Such polymorphic declarations are replaced by type-instantiated
--- monomorphic definitions before printing an SMT script.
data Command = Assert              Term
             | CheckSat
             | Comment             String
             | DeclareVar          SortedVar
             | DeclareDatatypes    [(Ident, Int, DTDecl)] -- name/arity/decls
             | DeclareFun          Ident [Sort] Sort
             | DeclareSort         Ident Int
             | DefineFunsRec       [(FunDec, Term)]
             | DefineSigsRec       [FunSigTerm]
             | EmptyLine
  deriving (Eq, Show)

-- Smart constructors:

--- Assert a simplified formula.
sAssert :: Term -> Command
sAssert = Assert . simpTerm

--- Examples:
{-
listType =
  DeclareDatatypes 
    [("List",1,
      DT ["T"]
         [ DCons "nil" [],
           DCons "cons" [("car", SComb "T" []),
                         ("cdr", SComb "List" [SComb "T" []])]])]

maybeType =
  DeclareDatatypes 
    [("Maybe",1,
      DT ["T"]
         [ DCons "Nothing" [],
           DCons "Just" [("just", SComb "T" [])]])]

pairType =
  DeclareDatatypes 
    [("Pair",2,
      DT ["X", "Y"]
         [ DCons "mk-pair" [("first",  SComb "X" []),
                            ("second", SComb "Y" [])]])]
-}

---------------------------------------------------------------------------
-- All possibly sorted identifiers occurring in a SMT term.
allQIdsOfTerm :: Term -> [QIdent]
allQIdsOfTerm (TConst _)     = []
allQIdsOfTerm (TSVar _)      = []
allQIdsOfTerm (TComb f args) = foldr union [f] (map allQIdsOfTerm args)
allQIdsOfTerm (Forall _ arg) = allQIdsOfTerm arg
allQIdsOfTerm (Exists _ arg) = allQIdsOfTerm arg
allQIdsOfTerm (Let bs e)     =
  foldr union [] (map allQIdsOfTerm (e : map snd bs))
allQIdsOfTerm (Match  e ps)     =
  foldr union [] (map allQIdsOfTerm (e : map snd ps))

-- All possibly sorted identifiers occurring in a define-sig element.
allQIdsOfSigs :: [FunSigTerm] -> [QIdent]
allQIdsOfSigs = foldr union [] . map allQIdsOfSig
 where allQIdsOfSig (_,_,t) = allQIdsOfTerm t

-- TODO: should be extended to all commands but currently sufficient
allQIdsOfAsserts :: [Command] -> [QIdent]
allQIdsOfAsserts = foldr union [] . map allQIdsOfAssert

allQIdsOfAssert :: Command -> [QIdent]
allQIdsOfAssert cmd = case cmd of Assert t -> allQIdsOfTerm t
                                  _        -> []

---------------------------------------------------------------------------
--- All type parameters occurring in a sort.
typeParamsOfSort :: Sort -> [Ident]
typeParamsOfSort s@(SComb sn ss) =
  if isTypeParameter s then [sn]
                       else foldr union [] (map typeParamsOfSort ss)

--- All type parameters contained in a term.
typeParamsOfTerm :: Term -> [Ident]
typeParamsOfTerm (TConst _) = []
typeParamsOfTerm (TSVar  _) = []
typeParamsOfTerm (TComb f args) = foldr union (typeParamsOfQId f)
                                        (map typeParamsOfTerm args)
typeParamsOfTerm (Forall svs arg) =
  foldr union (typeParamsOfTerm arg) (map typeParamsOfSV svs)
typeParamsOfTerm (Exists svs arg) =
  foldr union (typeParamsOfTerm arg) (map typeParamsOfSV svs)
typeParamsOfTerm (Let bs e)     =
  foldr union [] (map typeParamsOfTerm (e : map snd bs))
typeParamsOfTerm (Match e ps)     =
  foldr union [] (map typeParamsOfTerm (e : map snd ps))

typeParamsOfQId :: QIdent -> [Ident]
typeParamsOfQId (Id _  ) = []
typeParamsOfQId (As _ s) = typeParamsOfSort s

typeParamsOfSV :: SortedVar -> [Ident]
typeParamsOfSV (SV _ s) = typeParamsOfSort s

typeParamsOfFunSig :: FunSig -> [Ident]
typeParamsOfFunSig (FunSig _ ss s) =
  foldr union [] (map typeParamsOfSort (ss++[s]))

--- A type parameter substitution.
type TPSubst = FM.Map Ident Sort

--- The empty substitution
emptyTPSubst :: TPSubst
emptyTPSubst = FM.empty

--- Shows a type substitution.
showTPSubst :: TPSubst -> String
showTPSubst ts =
  "{ " ++
  intercalate ", " (map (\(i,s) -> show i ++ " |-> " ++ show s) (FM.toList ts))
  ++ " }"

--- Create a type substitution from ident/sort pairs.
makeTPSubst :: [(Ident,Sort)] -> TPSubst
makeTPSubst = FM.fromList

----------------------------------------------------------------------------
--- Compute sort matching, i.e., if `matchSort t1 t2 = s`, then `t2 = s(t1)`.
matchSort :: Sort -> Sort -> Maybe TPSubst
matchSort s1@(SComb sn1 ss1) s2@(SComb sn2 ss2)
 | isAnonymousType s2
 = Just emptyTPSubst
 | isTypeParameter s1
 = Just $ if s1 == s2
            then emptyTPSubst
            else FM.insert (head (typeParamsOfSort s1)) s2 emptyTPSubst
 | otherwise
 = if sn1 == sn2 then matchSorts ss1 ss2 else Nothing

matchSorts :: [Sort] -> [Sort] -> Maybe TPSubst
matchSorts []       []       = Just emptyTPSubst
matchSorts []       (_:_)    = Nothing
matchSorts (_:_)    []       = Nothing
matchSorts (t1:ts1) (t2:ts2) = do
  s <- matchSort t1 t2
  t <- matchSorts (map (substSort s) ts1)(map (substSort s) ts2)
  return (FM.union s t)

--- Applies a sort substitution to a sort.
substSort :: TPSubst -> Sort -> Sort
substSort sub (SComb sn ss) =
  maybe (SComb sn (map (substSort sub) ss)) id (FM.lookup sn sub)

--- Applies a sort substitution to a term.
substTerm :: TPSubst -> Term -> Term
substTerm sub term = case term of
  TConst _ -> term
  TSVar  _ -> term
  TComb f args -> TComb (substQId sub f) (map (substTerm sub) args)
  Forall svs arg -> Forall (map (substSV sub) svs) (substTerm sub arg)
  Exists svs arg -> Exists (map (substSV sub) svs) (substTerm sub arg)
  Let bs e -> Let (map (\ (v,s) -> (v, substTerm sub s)) bs) (substTerm sub e)
  Match e ps -> Match (substTerm sub e) (map (\(v,s) -> (v, substTerm sub s)) ps)

substQId :: TPSubst -> QIdent -> QIdent
substQId _ qid@(Id _) = qid
substQId sub (As n s) = As n (substSort sub s)

substSV :: TPSubst -> SortedVar -> SortedVar
substSV sub (SV v s) = SV v (substSort sub s)

substFunSig :: TPSubst -> FunSig -> FunSig
substFunSig sub (FunSig fn ss s) =
  FunSig fn (map (substSort sub) ss) (substSort sub s)

substDefSig :: TPSubst -> FunSigTerm -> FunSigTerm
substDefSig tsub (ps, fsig, term) =
  (ps \\ FM.keys tsub, substFunSig tsub fsig, substTerm tsub term)

--------------------------------------------------------------------------
-- Rename identifiers.

rnmTerm :: (Ident -> Ident) -> Term -> Term
rnmTerm rnm term = case term of
  TConst _ -> term
  TSVar  _ -> term
  TComb f args -> TComb (rnmQId rnm f) (map (rnmTerm rnm) args)
  Forall svs arg -> Forall svs (rnmTerm rnm arg)
  Exists svs arg -> Exists svs (rnmTerm rnm arg)
  Let bs e -> Let (map (\ (v,s) -> (v, rnmTerm rnm s)) bs) (rnmTerm rnm e)
  Match e ps -> Match (rnmTerm rnm e) (map (\ (v,s) -> (v, rnmTerm rnm s)) ps)

rnmQId :: (Ident -> Ident) -> QIdent -> QIdent
rnmQId rnm (Id n)   = Id (rnm n)
rnmQId rnm (As n s) = As (rnm n) s

rnmFunSig :: (Ident -> Ident) -> FunSig -> FunSig
rnmFunSig rnm (FunSig fn ss s) = FunSig (rnm fn) ss s

rnmDefSig :: (Ident -> Ident) -> ([Ident],FunSig,Term) -> ([Ident],FunSig,Term)
rnmDefSig rnm (ps, fsig, term) =
  (ps, rnmFunSig rnm fsig, rnmTerm rnm term)

--------------------------------------------------------------------------
-- A simplifier for terms:
simpTerm :: Term -> Term
simpTerm (TConst l) = TConst l
simpTerm (TSVar  v) = TSVar v
simpTerm (Let bs t) = if null bs then t'
                                 else Let bs' t'
 where bs' = map (\ (v,tm) -> (v, simpTerm tm)) bs
       t'  = simpTerm t
simpTerm (Match t ps) = Match t' ps'
 where t'  = simpTerm t
       ps' = map (\ (v,tm) -> (v, simpTerm tm)) ps
simpTerm (Forall vs t) = if null vs then t' else Forall vs t'
 where t' = simpTerm t
simpTerm (Exists vs t) = if null vs then t' else Exists vs t'
 where t' = simpTerm t
simpTerm (TComb f ts)
 | qidName f == "/=" && length ts == 2
 = simpTerm (TComb (Id "not") [TComb (Id "=") ts])
 | f == Id "apply" && not (null ts')
 = case head ts' of TComb s' ts0 -> TComb s' (ts0 ++ tail ts')
                    _            -> fts
 | f == Id "not"
 = case ts' of [TComb s' [ts0]] -> if s' == f then ts0 else fts
               _                -> fts
 | f == Id "and"
 = case filter (/= tTrue) ts' of
          []  -> tTrue
          cjs -> if tFalse `elem` cjs
                   then tFalse
                   else TComb f (concatMap joinSame cjs)
 | f == Id "or"
 = case filter (/= tFalse) ts' of
          []  -> tFalse
          djs -> if tTrue `elem` djs
                   then tTrue
                   else TComb f (concatMap joinSame djs)
 | otherwise = fts
 where
  ts' = map simpTerm ts
  fts = TComb f ts'

  joinSame arg = case arg of TComb f' args | f==f' -> args
                             _                     -> [arg]

--------------------------------------------------------------------------
--- Remove As-identifiers if they are functions (for better readability):
reduceAsInTerm :: Term -> Term
reduceAsInTerm (TConst l) = TConst l
reduceAsInTerm (TSVar  v) = TSVar v
reduceAsInTerm (Let bs t) = Let (map (\ (v,tm) -> (v, reduceAsInTerm tm)) bs)
                                (reduceAsInTerm t)
reduceAsInTerm (Match t ps)  = Match (reduceAsInTerm t)
                                 (map (\ (v,tm) -> (v, reduceAsInTerm tm)) ps)
reduceAsInTerm (Forall vs t) = Forall vs (reduceAsInTerm t)
reduceAsInTerm (Exists vs t) = Exists vs (reduceAsInTerm t)
reduceAsInTerm (TComb f ts)  = TComb (simpAs f) (map reduceAsInTerm ts)
 where
  simpAs qid = case qid of As n (SComb s _) | s == "Func" -> Id n
                           _ -> qid

--- Remove As-identifiers if they are functions (for better readability):
reduceAsInCmd :: Command -> Command
reduceAsInCmd cmd = case cmd of
  Assert t         -> Assert (reduceAsInTerm t)
  DefineFunsRec fs -> DefineFunsRec
                        (map (\(fd,t) -> (fd, reduceAsInTerm t)) fs)
  DefineSigsRec fs -> DefineSigsRec
                        (map (\(is,fd,t) -> (is, fd, reduceAsInTerm t)) fs)
  _                -> cmd

--------------------------------------------------------------------------
-- Get all sort identifiers occurring in a sort.
sortIdsOfSort :: Sort -> [Ident]
sortIdsOfSort (SComb s ss) = s : concatMap sortIdsOfSort ss

-- Get all sorts occurring in a term.
sortsOfTerm :: Term -> [Sort]
sortsOfTerm (TConst _)    = []
sortsOfTerm (TSVar  _)    = []
sortsOfTerm (Let bs t)    = concatMap (sortsOfTerm . snd) bs ++ sortsOfTerm t
sortsOfTerm (Match t ps)  = sortsOfTerm t ++ concatMap (sortsOfTerm . snd) ps
sortsOfTerm (Forall vs t) = map sortOfSortedVar vs ++ sortsOfTerm t
sortsOfTerm (Exists vs t) = map sortOfSortedVar vs ++ sortsOfTerm t
sortsOfTerm (TComb f ts)  = sortsOfQIdent f ++ concatMap sortsOfTerm ts
 where
  sortsOfQIdent (Id _)   = []
  sortsOfQIdent (As _ s) = [s]

sortOfSortedVar :: SortedVar -> Sort
sortOfSortedVar (SV _ s) = s

--------------------------------------------------------------------------
-- Remove parametric polymorphism (supported by `DefineSigsRec`)
-- in an SMT script.
-- First, for all QIdents occurring in assertions, their type-instantiated
-- signatures are added. Then, for all QIdents occurring in these added
-- operations, their type-instantiated signatures are added and so forth,
-- until nothing needs to be added. Finally, the type-instantiated signatures
-- are renamed.
unpoly :: [Command] -> [Command]
unpoly commands =
   let allsigs = map sigNameSort (allSigs commands)
   in map (unpolyCmd allsigs) . reverse . addSigs [] . reverse $ commands
 where
  addSigs _    []         = []
  addSigs qids (cmd:cmds) = case cmd of
    DefineSigsRec fts ->
      let (qids1,ftss) = addAllInstancesOfSigs (union (allQIdsOfSigs fts) qids)
                                               fts
      in DefineSigsRec ftss : addSigs qids1 cmds
    _ -> cmd : addSigs (union (allQIdsOfAssert cmd) qids) cmds

  -- rename qualified names according to their sorts
  unpolyCmd sigs cmd = case cmd of
    DefineSigsRec fts -> DefineSigsRec $ map rnmTermInSig fts
    Assert term       -> Assert (rnmQIdWithTInstTerm sigs term)
    _ -> cmd
   where
    rnmTermInSig (ps,sig,term) = (ps, sig, rnmQIdWithTInstTerm sigs term)

-- Transforms a list of signatures into all its instances required by
-- sorted identifiers (second argument) and also required by sorted
-- identifiers in the added instances. Returns also the list of
-- remaining identifiers.
addAllInstancesOfSigs :: [QIdent] -> [FunSigTerm] -> ([QIdent], [FunSigTerm])
addAllInstancesOfSigs allqids = addAllInsts allqids
 where
  addAllInsts qids fts =
    let (qids1,fts1) = addInstancesOfSigs qids fts
    in if null fts1
         then (qids1,fts)
         else let (qids2,fts2) = addAllInsts
                                   (union qids1 (allQIdsOfSigs fts1 \\ allqids))
                                   (fts ++ fts1)
              in (qids2, fts2)

-- Adds to given (polymorphic) define-sig elements all its type instances
-- required by qualified identifiers occurring in the first argument
-- provided that it does not already occur in the sig elements.
-- The list of unused qualified identifiers is also returned.
addInstancesOfSigs :: [QIdent] -> [FunSigTerm] -> ([QIdent], [FunSigTerm])
addInstancesOfSigs qids allsigs = addInstsOfSigs qids allsigs
 where
  addInstsOfSigs qids0 []         = (qids0,[])
  addInstsOfSigs qids0 (fts:ftss) =
    let (qids1,fts1) = addInstancesOfSig qids0 allsigs fts
        (qids2,fts2) = addInstsOfSigs qids1 ftss
    in (qids2, fts1 ++ fts2)

-- Adds to a given (polymorphic) define-sig element all its type instances
-- required by qualified identifiers occurring in the first argument
-- provided that it does not already occur in the sig elements
-- contained in the second argument.
-- The list of unused qualified identifiers is also returned.
addInstancesOfSig :: [QIdent] -> [FunSigTerm] -> FunSigTerm
                  -> ([QIdent], [FunSigTerm])
addInstancesOfSig allqids allsigs fts@(ps, (FunSig fn ss rs), _) =
  addSigInsts allqids
 where
  addSigInsts []         = ([],[])
  addSigInsts (qid:qids) =
    let (qids1,sigs1) = addSigInsts qids
    in case qid of
         As n s | n==fn -> (qids1, sigInstForType s ++ sigs1)
         _              -> (qid : qids1, sigs1)

  sigInstForType s =
    maybe []
          (\tsub -> let rnm = toTInstName fn ps tsub
                    in if rnm fn `elem` map nameOfSig allsigs
                         then []
                         else [(rnmDefSig rnm (substDefSig tsub fts))])
          (matchSort (sigTypeAsSort ss rs) s)

--------------------------------------------------------------------------

-- Rename a sorted name w.r.t. its type instance of the polymorphic function.
-- For instance,
--     (As "id" (SComb "Func" [SComb "Int" [], SComb "Int" []]))
-- will be renamed to
--     (As "id_Int" (SComb "Func" [SComb "Int" [], SComb "Int" []]))
rnmQIdWithTInst :: [(Ident, ([Ident],Sort))] -> QIdent -> QIdent
rnmQIdWithTInst _ (Id n) = Id n
rnmQIdWithTInst sigs qid@(As n s) =
  maybe qid
        (\ (ps,psort) -> maybe qid
                               (\tsub -> As (addTInstName ps tsub n) s)
                               (matchSort psort s))
        (lookup n sigs)

-- Rename all sorted names occurring in a term w.r.t. its type instance
-- of the polymorphic function.
rnmQIdWithTInstTerm :: [(Ident, ([Ident],Sort))] -> Term -> Term
rnmQIdWithTInstTerm sigs term = case term of
  TConst _ -> term
  TSVar  _ -> term
  TComb f args -> TComb (rnmQIdWithTInst sigs f)
                        (map (rnmQIdWithTInstTerm sigs) args)
  Forall svs arg -> Forall svs (rnmQIdWithTInstTerm sigs arg)
  Exists svs arg -> Exists svs (rnmQIdWithTInstTerm sigs arg)
  Let bs e -> Let (map (\ (v,s) -> (v, rnmQIdWithTInstTerm sigs s)) bs)
                  (rnmQIdWithTInstTerm sigs e)
  Match e ps -> Match (rnmQIdWithTInstTerm sigs e)
                      (map (\ (v,s) -> (v, rnmQIdWithTInstTerm sigs s)) ps)
                  

-- Renaming operation which changes the name of a given (polymorphic)
-- function w.r.t. a list of type parameters and a substitution.
toTInstName :: Ident -> [Ident] -> TPSubst -> Ident -> Ident
toTInstName fn ps tsub n | fn == n   = addTInstName ps tsub n
                         | otherwise = n

-- Add a sort index to a name of a (polymorphic) function w.r.t.
-- a list of type parameters and a type substitution.
addTInstName :: [Ident] -> TPSubst -> Ident -> Ident
addTInstName tps tsub n =
  n ++ concatMap (\p -> maybe "" (('_':) . showSort) (FM.lookup p tsub)) tps

-- All signatures in a list of commands.
allSigs :: [Command] -> [FunSigTerm]
allSigs = concatMap sigOfCmd
 where sigOfCmd cmd = case cmd of DefineSigsRec fts -> fts
                                  _                 -> []

-- The name of a signature.
nameOfSig :: FunSigTerm -> Ident
nameOfSig (_, FunSig n _ _, _) = n

-- The name and sort of a signature.
sigNameSort :: FunSigTerm -> (Ident, ([Ident],Sort))
sigNameSort (ps, FunSig n ss s, _) = (n, (ps, sigTypeAsSort ss s))

sigTypeAsSort :: [Sort] -> Sort -> Sort
sigTypeAsSort [] s = s
sigTypeAsSort (t:ts) s = SComb "Func" [t, sigTypeAsSort ts s]

--------------------------------------------------------------------------
-- Pretty printing:

--- Show an SMT-LIB script with a newline after transforming polymorphic
--- functions into type-instanteded functions.
showSMT :: [Command] -> String
showSMT cmds =
  pPrint (pretty (SMTLib (map reduceAsInCmd (unpoly cmds)))) ++ "\n"

--- Show an SMT-LIB script with a newline.
showSMTRaw :: [Command] -> String
showSMTRaw cmds = pPrint (pretty (SMTLib cmds)) ++ "\n"

instance Pretty SMTLib where
  pretty (SMTLib cmds) = vsep (map pretty cmds)

instance Pretty Sort where
  pretty (SComb i ss) = parensIf (not $ null ss) $
                          text i <+> (hsep (map pretty ss))

instance Pretty TLiteral where
  pretty (TInt    n) = int n
  pretty (TFloat  f) = float f
  pretty (TString s) = text s

instance Pretty QIdent where
  pretty (Id i  ) = text i
  pretty (As i s) = parent [text "as", text i, pretty s]

instance Pretty SortedVar where
  pretty (SV v s) = parent [prettyVar v, pretty s]

instance Pretty Pattern where
  pretty (PComb qi ts) = parensIf (not $ null ts) $
                           pretty qi <+> (hsep (map (pretty . TSVar) ts))

instance Pretty Term where
  pretty (TConst c) = pretty c
  pretty (TSVar  v) = prettyVar v
  pretty (TComb  qi ts) = parensIf (not $ null ts) $
                           pretty qi <+> (hsep (map pretty ts))
  pretty (Let     bs t) = parent [text "let", parent (map ppBind bs), pretty t]
    where ppBind (v, t') = parent [prettyVar v, pretty t']
  pretty (Match t ps) = case ps of
    [(p1,t1), (p2,t2)] | p1 == pTrue && p2 == pFalse -> pretty (tITE t t1 t2)
                       | p2 == pTrue && p1 == pFalse -> pretty (tITE t t2 t1)
    _ -> parent [text "match", pretty t, parent (map ppMatch ps)]
   where ppMatch (v, t') = parent [pretty v, pretty t']
  pretty (Forall svs t) = parent [ text "forall"
                                 , parent (map pretty svs)
                                 , pretty t
                                 ]
  pretty (Exists svs t) = parent [ text "exists"
                                 , parent (map pretty svs)
                                 , pretty t
                                 ]

instance Pretty DTDecl where
  pretty (DT tys cs) = if null tys
                         then parent (map pretty cs)
                         else parent [ text "par"
                                     , parent (map text tys)
                                     , parent (map pretty cs)
                                     ]

instance Pretty DTCons where
  pretty (DCons sym sels) = parent [text sym, (hsep (map prettySel sels))]
   where
    prettySel (n,s) = parent [text n, pretty s]

instance Pretty FunSig where
  pretty (FunSig fn ss s) = parent (ppCmd (DeclareFun fn ss s))

instance Pretty FunDec where
  pretty (FunDec fn svs s) = parent [ text fn, parent (map pretty svs)
                                    , pretty s
                                    ]

instance Pretty Command where
  pretty cmd = case cmd of
    Comment cmt -> semi <+> text cmt
    EmptyLine   -> text ""  
    DefineSigsRec fts -> vsep $ map (pretty . (\ (_,t,_) -> t)) fts ++
                                map ppSigBody fts
    _           -> parent $ ppCmd cmd

ppSigBody :: ([Ident],FunSig,Term) -> Doc
ppSigBody (_, FunSig fn _ _, term) = vsep $ map pretty
  [ EmptyLine, Comment $ "Axiomatization of function '" ++ fn ++ "'"
  , sAssert term ]

--- Pretty printing of SMT-LIB commands.
ppCmd :: Command -> [Doc]
ppCmd cmd = case cmd of
  Assert   t -> [text "assert", pretty t]
  CheckSat   -> [text "check-sat"]
  DeclareVar (SV v s)  -> [text "declare-const", prettyVar v, pretty s]
  DeclareDatatypes sds -> let (ss, ars, ds) = unzip3 sds in
                          [ text "declare-datatypes"
                          , parent (map (\ (s,a) -> parent [text s, int a])
                                        (zip ss ars))
                          , parent (map pretty ds)
                          ]
  DeclareFun fn ss s -> [ text "declare-fun"
                        , text fn
                        , parent (map pretty ss)
                        , pretty s
                        ]
  DefineFunsRec fts -> let (fs, ts) = unzip fts in
                       [ text "define-funs-rec"
                       , parent (map pretty fs)
                       , parent (map pretty ts)
                       ]
  DeclareSort sym n -> [text "declare-sort", text sym, int n]
  _          -> error $ "ppCmd: command '" ++ show cmd ++ "' not reachable!"

prettyVar :: SVar -> Doc
prettyVar v = text ('x' : show v)

--- Pretty print the given documents separated with spaces and parenthesized
parent :: [Doc] -> Doc
parent = encloseSep lparen rparen space

