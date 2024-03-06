-----------------------------------------------------------------------------
--- Some operations to translate FlatCurry operations into SMT assertions.
---
--- @author  Michael Hanus
--- @version March 2024
---------------------------------------------------------------------------

module Verify.WithSMT
 where

import Control.Monad     ( unless, when )
import Data.Either       ( partitionEithers, rights )
import Data.IORef
import Data.List         ( (\\), find, init, isPrefixOf, last, maximum, nub
                         , partition, union )
import Data.Maybe        ( catMaybes, fromMaybe, isJust )
import Numeric           ( readHex )
import System.CPUTime    ( getCPUTime )
import Debug.Trace

import Control.Monad.Trans.State
import Data.Tuple.Extra   ( both )
import FlatCurry.AddTypes
import FlatCurry.Build
import FlatCurry.Goodies
import FlatCurry.Names
import FlatCurry.Print
import FlatCurry.Simplify
import FlatCurry.Types as FC
import System.FilePath    ( (</>) )
import System.IOExts      ( evalCmd )
import Text.Pretty        ( pPrint, pretty, text )

import Verify.ESMT as SMT
import Verify.Helpers
import Verify.Options
import Verify.ProgInfo
import PackageConfig      ( getPackagePath )

------------------------------------------------------------------------------
-- Calls the SMT solver to check whether an assertion implies some
-- property (represented as FlatCurry expressions).
-- If the implication is `False`, the unsatisfiability of the assertion
-- is checked.
checkUnsatisfiabilityWithSMT :: Options -> QName -> String -> IORef ProgInfo
          -> [(QName,ConsInfo)] -> [(Int,TypeExpr)] -> Expr -> IO (Maybe Bool)
checkUnsatisfiabilityWithSMT opts qf scripttitle pistore consinfos
                             vartypes assertionexp = do
  let (cnames,fnames) = both nub
                             (partitionEithers (allQNamesInExp assertionexp))
      cnamesreq = filter (`notElem` [pre "False", pre "True", anonCons]) cnames
  --putStrLn $ "ASSERTION EXPRESSION: " ++ showExp assertionexp
  --putStrLn $ "NAMES IN ASSERTION: " ++ show (cnamesreq ++ fnames)
  loadModulesForQNames opts pistore (cnamesreq ++ fnames)
  pinfos <- fmap progInfos $ readIORef pistore
  let typedassertion = addTypes2VarExp pinfos vartypes assertionexp fcBool
  --putStrLn $ "TYPED ASSERTION EXPRESSION: " ++ showExp typedassertion
  let foassertexp   = replaceHigherOrderInExp (simpExpr typedassertion)
      foassertfuncs = rights (allQNamesInExp foassertexp)
  --putStrLn $ "SIMPLE TYPED ASSERTION EXPRESSION: " ++ showExp foassertexp
  maybe
    (transExpError typedassertion)
    (\ (assertion,varsorts) ->
       catch (checkUnsatWithSMT opts qf scripttitle pistore consinfos vartypes
                                varsorts assertion cnamesreq foassertfuncs)
             (\e -> print e >> return Nothing))
    (exp2SMTWithVars (maximum (0 : map fst vartypes))
                     Nothing foassertexp)
 where
  transExpError e = do putStrLn $ "Cannot translate expression:\n" ++ showExp e
                       return Nothing

checkUnsatWithSMT :: Options -> QName -> String -> IORef ProgInfo
                  -> [(QName,ConsInfo)] 
                  -> [(Int,TypeExpr)] -> [(Int,Sort)]
                  -> Term -> [QName] -> [QName] -> IO (Maybe Bool)
checkUnsatWithSMT opts qf title pistore consinfos vartypes
                  extravars      -- variables representing h.o. subexps
                  assertion      -- assertion to be checked
                  assertioncons  -- constructors occurring in the assertion
                  assertfuncs =  -- defined functions occurring in assertion
  flip catch (\e -> print e >> return Nothing) $ do
  --let allsyms = nub (catMaybes
  --                     (map (\n -> maybe Nothing Just (untransOpName n))
  --                          (map qidName (allQIdsOfTerm assertion))))
  unless (null assertfuncs) $ printWhenDetails opts $
    "Translating operations into SMT: " ++ unwords (map showQName assertfuncs)
  fdecls0 <- getAllFunctions opts pistore assertfuncs
  pinfos <- fmap progInfos $ readIORef pistore
  let fdecls1 = addTypes2FuncDecls pinfos
                 (map (completeBranchesInFunc consinfos True) fdecls0)
      -- reduce to functions reachable from assertion after eliminating h.o.:
      fdecls  = usedFunctions assertfuncs
                  (map (updFuncBody replaceHigherOrderInExp) fdecls1)
  --putStrLn $ "OPERATIONS TO BE TRANSLATED:\n" ++ unlines (map showFuncDecl fdecls)
  let smtfuncs = maybe (Comment $ "ERROR translating " ++
                                  show (map funcName fdecls))
                       (\fds -> DefineSigsRec fds)
                       (mapM fun2SMT fdecls)
      fdecltvars = nub (concatMap allTVarsInFuncDecl fdecls)
  --putStrLn $ "TRANSLATED FUNCTIONS:\n" ++ pPrint (pretty smtfuncs)
  --let title1 = title ++ "\nTRANSLATED FUNCTIONS:\n" ++ pPrint (pretty smtfuncs)
  let vartypestcons = foldr union [] (map (tconsOfTypeExpr . snd) vartypes)
      funcstcons    = foldr union [] (map (tconsOfTypeExpr . funcType) fdecls)
      asserttcons   = map (\(ConsType _ tc _) -> tc)
                          (map (snd3 . infoOfCons consinfos) assertioncons)
      (primtypes,usertypes) =
         partition ((== "Prelude") . fst)
                   (union funcstcons (union vartypestcons asserttcons))
  decls <- mapM (getTypeDeclOf pistore) usertypes
  -- collect all type parameters in order to declare them as sorts:
  let tvarsInVars = foldr union []
                          (map (typeParamsOfSort . type2sort)
                          (map snd vartypes ++ map TVar fdecltvars))
      varsorts = map (\(i,te) -> (i, type2sort te)) vartypes ++ extravars
  --putStrLn $ "Assertion: " ++ pPrint (pretty assertion)
  let smt   = concatMap preludeType2SMT (map snd primtypes) ++
              [ EmptyLine ] ++
              (if null decls
                 then []
                 else [ Comment "User-defined datatypes:" ] ++
                      map tdecl2SMT decls) ++
              (if null tvarsInVars
                 then []
                 else [ EmptyLine, Comment "Polymorphic sorts:" ] ++
                      map (\tv -> DeclareSort tv 0) tvarsInVars) ++
              [ EmptyLine, smtfuncs, EmptyLine
              , Comment "Free variables:" ] ++
              map (\(i,s) -> DeclareVar (SV i s)) varsorts ++
              [ EmptyLine
              , Comment "Boolean formula of assertion (known properties):"
              , sAssert assertion, EmptyLine
              , Comment "check satisfiability:"
              , CheckSat
              ]
  --putStrLn $ "SMT commands as Curry term:\n" ++ show smt
  pp <- getPackagePath
  smtprelude <- readFile (pp </> "include" </>
                          if all ((`elem` defaultSMTTypes) . snd) primtypes
                            then "Prelude_min.smt"
                            else "Prelude.smt")
  let scripttitle = unlines (map ("; "++) (lines title))
  printWhenAll opts $
    "RAW SMT SCRIPT:\n" ++ scripttitle ++ "\n\n" ++ showSMTRaw smt
  let smtinput = scripttitle ++ "\n" ++ smtprelude ++ showSMT smt
  printWhenDetails opts $ "SMT SCRIPT:\n" ++ showWithLineNums smtinput
  let z3opts = ["-smt2", "-T:2"]
  when (optStoreSMT opts) $ storeSMT "SMT-" z3opts smtinput
  printWhenDetails opts $
    "CALLING Z3 (with options: " ++ unwords z3opts ++ ")..."
  (ecode,out,err) <- evalCmd "z3" ("-in" : z3opts) smtinput
  when (ecode > 0) $ do
    printWhenStatus opts $ "EXIT CODE: " ++ show ecode
    storeSMT "smterror-" z3opts smtinput
    when (optVerb opts < 3) $ printWhenStatus opts $
      "ERROR in SMT script (saved in 'error.smt'):\n" ++ out ++ "\n" ++ err
  printWhenDetails opts $ "RESULT:\n" ++ out
  unless (null err) $ printWhenDetails opts $ "ERROR:\n" ++ err
  let pcvalid = let ls = lines out in not (null ls) && head ls == "unsat"
  return (if ecode>0 then Nothing else Just pcvalid)
 where
  defaultSMTTypes = ["Int","Float","Bool", "Char", "[]"]

  storeSMT fileprefix z3opts script = do
    ctime <- getCPUTime
    let outfile = fileprefix ++ transOpName qf ++ "-" ++ show ctime ++ ".smt"
        execcmt = unwords $ ["; Run with: z3"] ++ z3opts ++ [outfile]
    writeFile outfile (execcmt ++ "\n\n" ++ script)

-- Translate a typed variable into an SMT declaration:
typedVar2SMT :: (Int,TypeExpr) -> Command
typedVar2SMT (i,te) = DeclareVar (SV i (type2sort te))

-- Gets all type constructors occurring in a type expression.
tconsOfTypeExpr :: TypeExpr -> [QName]
tconsOfTypeExpr (TVar _) = []
tconsOfTypeExpr (FuncType a b) =  union (tconsOfTypeExpr a) (tconsOfTypeExpr b)
tconsOfTypeExpr (TCons qName texps) =
  foldr union [qName] (map tconsOfTypeExpr texps)
tconsOfTypeExpr (ForallType _ te) =  tconsOfTypeExpr te

------------------------------------------------------------------------------
-- Get all qualified names occurring in an expression which are either
-- constructor or defined function names.
allQNamesInExp :: Expr -> [Either QName QName]
allQNamesInExp e =
  trExpr (const id) (const id) comb lt fr (.) cas branch const e []
 where
  comb ct qn exp = ((classifyName ct) qn:) . foldr (.) id exp
   where classifyName FuncCall         = Right
         classifyName (FuncPartCall _) = Right
         classifyName ConsCall         = Left
         classifyName (ConsPartCall _) = Left
  lt bs exp = exp . foldr (.) id (map snd bs)
  fr _ exp = exp
  cas _ exp bs = exp . foldr (.) id bs
  branch pat exp = ((args pat)++) . exp
  args (Pattern qc _) = [Left qc]
  args (LPattern _)   = []

------------------------------------------------------------------------------
--- Shows a text with line numbers prefixed:
showWithLineNums :: String -> String
showWithLineNums txt =
  let txtlines  = lines txt
      maxlog    = ilog (length txtlines + 1)
      showNum n = (take (maxlog - ilog n) (repeat ' ')) ++ show n ++ ": "
  in unlines . map (uncurry (++)) . zip (map showNum [1..]) $ txtlines

--- The value of `ilog n` is the floor of the logarithm
--- in the base 10 of `n`.
--- Fails if `n &lt;= 0`.
--- For positive integers, the returned value is
--- 1 less the number of digits in the decimal representation of `n`.
---
--- @param n - The argument.
--- @return the floor of the logarithm in the base 10 of `n`.
ilog :: Int -> Int
ilog n | n>0 = if n<10 then 0 else 1 + ilog (n `div` 10)

---------------------------------------------------------------------------
--- Translates a type declaration into an SMT datatype declaration.
tdecl2SMT :: TypeDecl -> Command
tdecl2SMT (TypeSyn tc _ _ _) =
  error $ "Cannot translate type synonym '" ++ showQName tc ++ "' into SMT!"
tdecl2SMT (TypeNew tc _ _ _) =
  error $ "Cannot translate newtype '" ++ showQName tc ++ "' into SMT!"
tdecl2SMT (Type tc _ tvars consdecls) =
  DeclareDatatypes
   [(tcons2SMT tc, length tvars,
     DT (map (\ (v,_) -> 'T' : show v) tvars) (map tconsdecl consdecls))]
 where
  tconsdecl (Cons qn _ _ texps) =
    let cname = transOpName qn
    in DCons cname (map (texp2sel qn) (zip [1..] texps))

  texp2sel cname (i,texp) = (genSelName cname i, type2sortD True texp)

--- Generates the name of the i-th selector for a given constructor.
genSelName :: QName -> Int -> String
genSelName qc@(mn,fn) i
 | mn == "Prelude" && take 3 fn == "(,,"
 = transOpName qc ++ "_" ++ show i
 | otherwise
 = "sel" ++ show i ++ '-' : transOpName qc

--- Translates a prelude type into an SMT datatype declaration,
--- if necessary.
preludeType2SMT :: String -> [Command]
preludeType2SMT tn
 | take 3 tn == "(,,"
 = let arity = length tn -1
   in [ Comment "Declaration of tuple type:"
      , DeclareDatatypes
        [(tcons2SMT (pre tn), arity,
          DT (map (\v -> 'T' : show v) [1 .. arity])
             [DCons (transOpName (pre tn)) (map texp2sel [1 .. arity])])]]
 | otherwise
 = []
 where
  texp2sel i = (genSelName (pre tn) i, SComb ('T' : show i) [])

---------------------------------------------------------------------------
-- Translates a function declaration into a (possibly polymorphic)
-- SMT function declaration.
fun2SMT :: FuncDecl -> Maybe ([Ident],FunSig,Term)
fun2SMT (Func qn _ _ texp rule) = do
  let fsig = FunSig (transOpName qn)
                    (map type2sort (argTypes texp))
                    (type2sort (resultType texp))
  srule <- rule2SMT rule
  let tpars = union (typeParamsOfFunSig fsig) (typeParamsOfTerm srule)
  return (tpars, fsig, srule)
 where
  rule2SMT (External s) = return $
    tEqu (tComb (transOpName qn) []) (tComb ("External:" ++ s) [])
  rule2SMT (Rule vs exp) = do
    let isnd = ndExpr exp
        lhs  = tComb (transOpName qn) (map TSVar vs)
    (rhs,varsorts) <- exp2SMTWithVars (maximum (0:vs))
                                      (if isnd then Just lhs else Nothing)
                                      (simpExpr exp)
    return $
      Forall (map (\ (v,t) -> SV v (type2sort t))
                  (funcType2TypedVars vs texp))
             (Exists (map (\ (v,s) -> SV v s) varsorts)
                     (if isnd then rhs else tEqu lhs rhs))

--- Returns `True` if the expression is non-deterministic,
--- i.e., if `Or` or `Free` occurs in the expression.
ndExpr :: Expr -> Bool
ndExpr = trExpr (\_ -> False)
                (\_ -> False)
                (\_ _ nds -> or nds)
                (\bs nd -> nd || any snd bs)
                (\_ _ -> True)
                (\_ _ -> True)
                (\_ nd bs -> nd || or bs)
                (\_ -> id)
                (\nd _ -> nd)

-- Replace higher-order features, like occurrences of `Prelude.apply` and
-- partial applications, by `Prelude.failed` in an expression since they
-- cannot be handled by SMT. Later, occurrences of `Prelude.failed` in
-- SMT terms are replaced by fresh variables so that they are unspecified
-- values.
replaceHigherOrderInExp :: Expr -> Expr
replaceHigherOrderInExp =
  trExpr Var Lit updComb FC.Let Free Or Case Branch Typed
 where
  updComb ct qn args = case ct of
    FuncPartCall _ -> fcFailed
    ConsPartCall _ -> fcFailed
    FuncCall | qn == pre "apply" -> fcFailed
    _              -> Comb ct qn args

-- Translates a (Boolean) FlatCurry expression into an SMT expression.
-- If the second argument is an SMT expression, an equation between
-- this expression and the translated result expression is generated.
-- This is useful to axiomatize non-deterministic operations.
-- If successful, the translated SMT expression together with new variables
-- (which are replacements for higher-order applications) are returned.
-- The first argument is the maximum index of already used variables.
exp2SMTWithVars :: Int -> Maybe Term -> Expr -> Maybe (Term, [(Int,Sort)])
exp2SMTWithVars maxusedvar lhs exp =
  maybe Nothing
        (\t -> Just $ elimFailed maxusedvar t)
        (exp2SMT lhs (replaceHigherOrderInExp exp))

-- Translates a (Boolean) FlatCurry expression into an SMT expression.
-- If the first argument is an SMT expression, an equation between
-- this expression and the translated result expression is generated.
-- This is useful to axiomatize non-deterministic operations.
exp2SMT :: Maybe Term -> Expr -> Maybe Term
exp2SMT lhs exp = case exp of
  Var i          -> Just $ makeRHS (TSVar i)
  Lit l          -> Just $ makeRHS (lit2SMT l)
  Comb _ qf args -> mapM (exp2SMT Nothing) args >>= comb2SMT qf
  Case _ e bs -> do t <- exp2SMT Nothing e
                    bts <- mapM branch2SMT bs
                    return $ makeRHS (Match t bts)
  FC.Let bs e -> do tbs <- mapM (\(v,be) -> do t <- exp2SMT Nothing be
                                               return (v,t))
                                bs
                    t <- exp2SMT lhs e
                    return $ tLet tbs t
  Free _ _    -> Nothing --error "exp2SMT: Free"
  Typed e te  -> case e of
    Comb _ qf args | all isTyped args
       -> mapM (exp2SMT Nothing) args >>=
          return . makeRHS .
            TComb (As (transOpName qf)
                      (type2sort (foldr FuncType te (map exprType args))))
    _  -> exp2SMT lhs e
  Or    e1 e2 -> do t1 <- exp2SMT lhs e1
                    t2 <- exp2SMT lhs e2
                    return $ tDisj [t1,t2]
 where
  comb2SMT qf targs
    | qf `elem` map pre ["chr", "ord"] && length targs == 1
    = return $ makeRHS (head targs) -- chars are integers --> no conversion
    | otherwise
    = return $ makeRHS (tComb (transOpName qf) targs)

  makeRHS rhs = maybe rhs (\l -> tEqu l rhs) lhs

  branch2SMT (Branch (LPattern _) _) = Nothing -- literal patterns not supported
  branch2SMT (Branch (Pattern qf vs) e) = do
    t <- exp2SMT lhs e
    return (PComb (Id (transOpName qf)) vs, t)

--- Is a expression typed? (should go into FlatCurry.Goodies)
isTyped :: Expr -> Bool
isTyped e = case e of
  Typed _ _ -> True
  _         -> False

--- Gets the type of a typed expression. (should go into FlatCurry.Goodies)
exprType :: Expr -> TypeExpr
exprType e = case e of
  Typed _ te -> te
  _          -> error "FlatCurry.Goodies.exprType: not a typed expression"

--- Translates a literal into an SMT expression.
--- We represent character as ints.
lit2SMT :: Literal -> Term
lit2SMT (Intc i)   = TConst (TInt i)
lit2SMT (Floatc f) = TConst (TFloat f)
lit2SMT (Charc c)  = TConst (TInt (ord c))

----------------------------------------------------------------------------
-- Implementation of a transformation which replaces occurrences of
-- `Prelude_apply` by new fresh variables.

-- The state for this transformation.
data TransApplyState = TransApplyState
  { tsFreshVarIndex :: Int           -- fresh variable index
  , tsNewVars       :: [(Int,Sort)]  -- new typed variables
  }

type TAState a = State TransApplyState a

-- Transforms a term by replacing occurrences of
-- `Prelude_failed` with new fresh variables.
-- The first argument is the maximum index of already used variables.
elimFailed :: Int -> Term -> (Term, [(Int,Sort)])
elimFailed maxusedvar trm =
  let st0 = TransApplyState (maximum (maxusedvar : allVarsInTerm trm) + 1) []
      (ntrm,st1) = runState (elimFailedInTerm trm) st0
  in (ntrm, reverse (tsNewVars st1))

elimFailedInTerm :: Term -> TAState Term
elimFailedInTerm t = case t of
  TConst _      -> return t
  TSVar _       -> return t
  TComb (As n srt) [] | n == "Prelude_failed"
    -> do st <- get
          let fv = tsFreshVarIndex st
              fvt = (fv, srt) -- sort is type of `failed`
          put st { tsFreshVarIndex = tsFreshVarIndex st + 1
                 , tsNewVars = fvt : tsNewVars st }
          return (TSVar fv)
  TComb qid ts  -> mapM elimFailedInTerm ts >>= return . TComb qid
  SMT.Let bs bt -> do trbs <- mapM (elimFailedInTerm . snd) bs
                      trbt <- elimFailedInTerm bt
                      return $ SMT.Let (zip (map fst bs) trbs) trbt
  Forall vs te  -> elimFailedInTerm te >>= return . Forall vs
  Exists vs te  -> elimFailedInTerm te >>= return . Exists vs
  Match mt brs  -> do trmt <- elimFailedInTerm mt
                      trbs <- mapM (elimFailedInTerm . snd) brs
                      return $ Match trmt (zip (map fst brs) trbs)
                       
-- All variables occurring in a SMT term.
allVarsInTerm :: Term -> [SVar]
allVarsInTerm (TConst _)      = []
allVarsInTerm (TSVar v)       = [v]
allVarsInTerm (TComb _ args)  = foldr union [] (map allVarsInTerm args)
allVarsInTerm (Forall vs arg) = union (map varOfSV vs) (allVarsInTerm arg)
allVarsInTerm (Exists vs arg) = union (map varOfSV vs) (allVarsInTerm arg)
allVarsInTerm (SMT.Let bs e)  =
  foldr union (map fst bs) (map allVarsInTerm (e : map snd bs))
allVarsInTerm (Match e ps)    =
  foldr union [] (map allVarsInTerm (e : map snd ps) ++ map (patVars . fst) ps)
 where
  patVars (PComb _ vs) = vs

varOfSV :: SortedVar -> SVar
varOfSV (SV v _) = v

----------------------------------------------------------------------------
--- Translates a FlatCurry type expression into a corresponding SMT sort.
--- Type variables are translated into the sort `TVar` where a
--- type variable index is appended (`TVari`) in order to generate
--- a polymorphic sort (which will later be translated by the
--- SMT translator).
--- The types `TVar` and `Func` are defined in the SMT prelude
--- which is always loaded.
type2sort :: TypeExpr -> Sort
type2sort  = type2sortD False

--- Similarly as 'type2sort' but type variables are shown as `Ti`
--- if the first argument is true, which is used when generating
--- algebraic data tyep declarations.
type2sortD :: Bool -> TypeExpr -> Sort
type2sortD dt = t2s
 where
  t2s texp = case texp of
    TVar i           -> SComb ((if dt then "T" else "TVar") ++ show i) []
    TCons qc targs   -> SComb (tcons2SMT qc) (map t2s targs)
    FuncType dom ran -> SComb "Func" (map t2s [dom,ran])
    ForallType _ te  -> t2s te
     --error "Veriy.WithSMT.type2SMT: cannot translate ForallType"

--- Translates a FlatCurry type constructor name into SMT.
tcons2SMT :: QName -> String
tcons2SMT (mn,tc)
 | "_Dict#" `isPrefixOf` tc
 = "Dict" -- since we do not yet consider class dictionaries...
 | mn == "Prelude" && take 3 tc == "(,,"
 = "Tuple" ++ show (length tc - 1)
 | mn == "Prelude"
 = maybe (encodeSpecialChars tc) id (lookup tc transPrimTCons)
 | otherwise
 = mn ++ "_" ++ encodeSpecialChars tc

--- Primitive type constructors from the prelude and their SMT names.
transPrimTCons :: [(String,String)]
transPrimTCons =
  [("Int","Int")
  ,("Float","Real")
  ,("Char","Int")  -- Char is represented as Int
  ,("[]","List")
  ,("()","Unit")
  ,("(,)","Pair")
  ,("Maybe","Maybe")
  ,("Either","Either")
  ,("Ordering","Ordering")
  ]

--- Encode special characters in strings  
encodeSpecialChars :: String -> String
encodeSpecialChars = concatMap encChar
 where
  encChar c | c `elem` "#$%[]()!,"
            = let oc = ord c
              in ['%', int2hex (oc `div` 16), int2hex(oc `mod` 16)]
            | otherwise = [c]

  int2hex i = if i<10 then chr (ord '0' + i)
                      else chr (ord 'A' + i - 10)

--- Translates urlencoded string into equivalent ASCII string.
decodeSpecialChars :: String -> String
decodeSpecialChars [] = []
decodeSpecialChars (c:cs)
  | c == '%'  = let n = case readHex (take 2 cs) of
                          [(h,"")] -> h
                          _        -> 0
                in chr n : decodeSpecialChars (drop 2 cs)
  | otherwise = c : decodeSpecialChars cs

--- Translates a qualified FlatCurry name into an SMT string.
transOpName :: QName -> String
transOpName (mn,fn)
 | mn=="Prelude" = fromMaybe tname (lookup fn primNames)
 | otherwise     = tname
 where
  tname = mn ++ "_" ++ encodeSpecialChars fn

--- Translates a (translated) SMT string back into qualified FlatCurry name.
--- Returns Nothing if it was not a qualified name.
untransOpName :: String -> Maybe QName
untransOpName s =
  let (mn,ufn) = break (=='_') s
  in if null ufn
       then Nothing
       else Just (mn, decodeSpecialChars (tail ufn))

----------------------------------------------------------------------------
--- Some primitive names of the prelude and their SMT names.
primNames :: [(String,String)]
primNames =
  [ -- Operations
  ("&&","and")
  ,("||","or")
  ,("not","not")
  ,("==","=")
  ,("/=","/=")
  ,("===","=")
  ,("/==","/=")
  ,("=","=")
  ,("<","<")
  ,("<=","<=")
  ,(">",">")
  ,(">=",">=")
  ,("+","+")
  ,("-","-")
  ,("*","*")
  -- Constructors:
  ,("True","true")
  ,("False","false")
  ,("[]","nil")
  ,(":","insert")
  ,("()","unit")
  ,("(,)","mk-pair")
  ,("LT","LT")
  ,("EQ","EQ")
  ,("GT","GT")
  ,("Nothing","Nothing")
  ,("Just","Just")
  ,("Left","Left")
  ,("Right","Right")
  ,("_","_") -- for anonymous patterns in case expressions
  ] ++
  map (\i -> ('(' : take (i-1) (repeat ',') ++ ")", "Tuple" ++ show i)) [3..15]

------------------------------------------------------------------------------
--- Extract all user-defined FlatCurry functions that might be called
--- by a given list of function names provided as the last argument.
--- The second argument is an `IORef` to the currently loaded modules.
--- Its contents will be extended when necessary.
getAllFunctions :: Options -> IORef ProgInfo -> [QName] -> IO [FuncDecl]
getAllFunctions opts pistore newfuns = do
  mods <- fmap (map (miProg . snd) . progInfos) $ readIORef pistore
  getAllFuncs mods preloadedFuncDecls newfuns
 where
  getAllFuncs _       currfuncs [] = return (reverse currfuncs)
  getAllFuncs allmods currfuncs (newfun:newfuncs)
    | newfun `elem` excludedCurryOperations ||
      newfun `elem` map (pre . fst) primNames ||
      newfun `elem` map funcName currfuncs || isPrimOp newfun
    = getAllFuncs allmods currfuncs newfuncs
    | fst newfun `elem` map progName allmods -- module already loaded:
    = maybe (error $ "getAllFunctions: " ++ show newfun ++ " not found!")
            (\fdecl -> --print fdecl >>
                       getAllFuncs allmods (fdecl : currfuncs)
                         (newfuncs ++
                          filter (`notElem` excludedCurryOperations)
                                 (funcsOfFuncDecl fdecl)))
            (find (\fd -> funcName fd == newfun)
                  (maybe []
                         progFuncs
                         (find (\m -> progName m == fst newfun) allmods)))
    | otherwise -- we must load a new module
    = do let mname = fst newfun
         printWhenStatus opts $
           "Loading module '" ++ mname ++ "' for '"++ snd newfun ++"'"
         addModInfoFor pistore mname
         newmod <- fmap miProg $ getModInfoFor pistore mname
         getAllFuncs (newmod : allmods) currfuncs (newfun:newfuncs)

--- Removes from a list of function declarations the functions not used
--- by an initial list of function names.
--- It is assumed that the list of functions is already sorted by
--- dependencies (ealier functions might call later ones).
usedFunctions :: [QName] -> [FuncDecl] -> [FuncDecl]
usedFunctions _ [] = []
usedFunctions usedfns (fdecl : fdecls)
  | funcName fdecl `elem` usedfns
  = fdecl : usedFunctions (union (funcsOfFuncDecl fdecl) usedfns) fdecls
  | otherwise
  = usedFunctions usedfns fdecls

--- Extract all user-defined FlatCurry functions that might be called
--- by a given list of function names provided as the last argument.
--- The second argument is an `IORef` to the currently loaded modules.
--- Its contents will be extended when necessary.
loadModulesForQNames :: Options -> IORef ProgInfo -> [QName] -> IO ()
loadModulesForQNames opts pistore qns = mapM_ loadMod (nub (map fst qns))
 where
  loadMod m = do
    mloaded <- hasModInfoFor pistore m
    unless mloaded $ do -- we must load a new module
      printWhenStatus opts $ "Loading module '" ++ m ++ "'..."
      addModInfoFor pistore m

-- Pre-loaded operations from the prelude to avoid reading the prelude
-- for simple operations.
preloadedFuncDecls :: [FuncDecl]
preloadedFuncDecls =
  [Func (pre "id") 1 Public 
     (FuncType (TVar 0) (TVar 0))
     (Rule [1] (Var 1)),
   Func (pre  "not") 1  Public 
     (FuncType fcBool fcBool)
     (Rule  [1] (Case Flex (Var 1)
                  [Branch (Pattern (pre "True") [] ) fcFalse,
                   Branch (Pattern (pre "False") []) fcTrue])),
   Func (pre "null") 1 Public 
     (FuncType (fcList (TVar 0)) fcBool)
     (Rule [1] (Case Flex (Var 1)
                  [Branch (Pattern (pre "[]") [])   fcTrue,
                   Branch (Pattern (pre ":") [2,3]) fcFalse]))
  ]

--- Exclude character-related operations since characters are treated as
--- integers so that these operations are not required.
excludedCurryOperations :: [QName]
excludedCurryOperations =
  map pre ["apply", "failed", "chr", "ord"]

--- Returns the names of all functions occurring in the
--- body of a function declaration.
funcsOfFuncDecl :: FuncDecl -> [QName]
funcsOfFuncDecl fd =
  nub (trRule (\_ e -> funcsInExpr e) (\_ -> []) (funcRule fd))

------------------------------------------------------------------------------
