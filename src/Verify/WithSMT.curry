-----------------------------------------------------------------------------
--- Some operations to translate FlatCurry operations into SMT assertions.
---
--- @author  Michael Hanus
--- @version January 2024
---------------------------------------------------------------------------

module Verify.WithSMT
 where

import Control.Monad     ( unless, when )
import Data.IORef
import Data.List         ( find, init, isPrefixOf, last, nub, partition, union )
import Data.Maybe        ( catMaybes, fromMaybe, isJust )
import Numeric           ( readHex )
import System.CPUTime    ( getCPUTime )
import Debug.Trace

import FlatCurry.AddTypes
import FlatCurry.Build
import FlatCurry.Files   ( readFlatCurry )
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
                             -> [(Int,TypeExpr)] -> Expr -> IO (Maybe Bool)
checkUnsatisfiabilityWithSMT opts qf scripttitle pistore
                             vartypes assertionexp = do
  let qns = filter (/= anonCons) (allQNamesInExp assertionexp)
  --putStrLn $ "ASSERTION EXPRESSION: " ++ showExp assertionexp
  --putStrLn $ "NAMES IN ASSERTION: " ++ show qns
  loadModulesForQNames opts pistore qns
  pinfos <- fmap progInfos $ readIORef pistore
  let typedexp = addTypes2VarExp pinfos vartypes assertionexp fcBool
  --putStrLn $ "TYPED ASSERTION EXPRESSION: " ++ showExp typedexp
  maybe
    (transExpError typedexp)
    (\assertion ->
       catch (checkUnsatWithSMT opts qf scripttitle pistore vartypes assertion)
             (\e -> print e >> return Nothing))
    (exp2SMT Nothing (simpExpr typedexp))
 where
  transExpError e = do putStrLn $ "Cannot translate expression:\n" ++ showExp e
                       return Nothing

-- Get all qualified names occurring in an expression.
allQNamesInExp :: Expr -> [QName]
allQNamesInExp e =
  trExpr (const id) (const id) comb lt fr (.) cas branch const e []
 where
  comb _ qn exp = (qn:) . foldr (.) id exp
  lt bs exp = exp . foldr (.) id (map snd bs)
  fr _ exp = exp
  cas _ exp bs = exp . foldr (.) id bs
  branch pat exp = ((args pat)++) . exp
  args (Pattern qc _) = [qc]
  args (LPattern _)   = []


checkUnsatWithSMT :: Options -> QName -> String -> IORef ProgInfo
                  -> [(Int,TypeExpr)] -> Term -> IO (Maybe Bool)
checkUnsatWithSMT opts qf title pistore vartypes assertion =
  flip catch (\e -> print e >> return Nothing) $ do
  let allsyms = nub (catMaybes
                       (map (\n -> maybe Nothing Just (untransOpName n))
                            (map qidName (allQIdsOfTerm assertion))))
  unless (null allsyms) $ printWhenDetails opts $
    "Translating operations into SMT: " ++ unwords (map showQName allsyms)
  fdecls0 <- getAllFunctions opts pistore allsyms
  pinfos <- fmap progInfos $ readIORef pistore
  let fdecls = addTypes2FuncDecls pinfos fdecls0
  --putStrLn $ "OPERATIONS TO BE TRANSLATED:\n" ++ unlines (map showFuncDecl fdecls)
  --smtfuncs <- funcs2SMT opts modsref allsyms
  let smtfuncs = maybe (Comment $ "ERROR translating " ++
                                  show (map funcName fdecls))
                       (\fds -> DefineSigsRec fds)
                       (mapM fun2SMT fdecls)
      fdecltvars = nub (concatMap allTVarsInFuncDecl fdecls)
  --putStrLn $ "TRANSLATED FUNCTIONS:\n" ++ pPrint (pretty smtfuncs)
  let vartypestcons = foldr union [] (map (tconsOfTypeExpr . snd) vartypes)
      funcstcons    = foldr union [] (map (tconsOfTypeExpr . funcType) fdecls)
      (pretypes,_ {-usertypes-}) =
         partition ((== "Prelude") . fst) (union funcstcons vartypestcons)
  let --decls = map (maybe (error "Internal error: some datatype not found!") id)
      --            [] --(map (tdeclOf vst) usertypes)
      -- collect of type parameters in order to delcare them as sorts:
      tvarsInVars = foldr union []
                          (map (typeParamsOfSort . type2sort)
                          (map snd vartypes ++ map TVar fdecltvars))
      varsorts = map (\(i,te) -> (i, type2sort te)) vartypes
  --putStrLn $ "Assertion: " ++ pPrint (pretty assertion)
  let smt   = --concatMap preludeType2SMT (map snd pretypes) ++
              [ EmptyLine ] ++
              --(if null decls
              --   then []
              --   else [ Comment "User-defined datatypes:" ] ++
              --        map tdecl2SMT decls) ++
              [ EmptyLine, Comment "Polymorphic sorts:" ] ++
              map (\tv -> DeclareSort tv 0) tvarsInVars ++
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
                  if all ((`elem` ["Int","Float","Bool", "Char", "[]"]) . snd)
                     pretypes then "Prelude_min.smt"
                              else "Prelude.smt")
  let scripttitle = unlines (map ("; "++) (lines title))
  printWhenAll opts $
    "RAW SMT SCRIPT:\n" ++ scripttitle ++ "\n\n" ++ showSMTRaw smt
  let smtinput = scripttitle ++ "\n" ++ smtprelude ++ showSMT smt
  printWhenDetails opts $ "SMT SCRIPT:\n" ++ showWithLineNums smtinput
  let z3opts = ["-smt2", "-T:2"]
  when (optStoreSMT opts) $ do
    ctime <- getCPUTime
    let outfile = "SMT-" ++ transOpName qf ++ "-" ++ show ctime ++ ".smt"
        execcmt = "; Run with: z3 " ++ unwords z3opts ++ " " ++ outfile ++ "\n\n"
    writeFile outfile (execcmt ++ smtinput)
  printWhenDetails opts $
    "CALLING Z3 (with options: " ++ unwords z3opts ++ ")..."
  (ecode,out,err) <- evalCmd "z3" ("-in" : z3opts) smtinput
  when (ecode > 0) $ do
    printWhenStatus opts $ "EXIT CODE: " ++ show ecode
    writeFile "error.smt" smtinput
    when (optVerb opts < 3) $ printWhenStatus opts $
      "ERROR in SMT script (saved in 'error.smt'):\n" ++ out ++ "\n" ++ err
  printWhenDetails opts $ "RESULT:\n" ++ out
  unless (null err) $ printWhenDetails opts $ "ERROR:\n" ++ err
  let pcvalid = let ls = lines out in not (null ls) && head ls == "unsat"
  return (if ecode>0 then Nothing else Just pcvalid)

-- Translate a typed variables to an SMT declaration:
typedVar2SMT :: (Int,TypeExpr) -> Command
typedVar2SMT (i,te) = DeclareVar (SV i (type2sort te))

-- Gets all type constructors of a type expression.
tconsOfTypeExpr :: TypeExpr -> [QName]
tconsOfTypeExpr (TVar _) = []
tconsOfTypeExpr (FuncType a b) =  union (tconsOfTypeExpr a) (tconsOfTypeExpr b)
tconsOfTypeExpr (TCons qName texps) =
  foldr union [qName] (map tconsOfTypeExpr texps)
tconsOfTypeExpr (ForallType _ te) =  tconsOfTypeExpr te

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
--- Translates a list of operations specified by their qualified name
--- (together with all operations on which these operation depend on)
--- into an SMT string that axiomatizes their semantics.
{-
funcs2SMT :: Options -> IORef [Prog] -> [QName] -> IO Command
funcs2SMT opts modsref qns = do
  -- get all relevant functions but exclude character related operations:
  funs <- getAllFunctions opts modsref (nub qns)
  return $ maybe (Comment $ "ERROR translating " ++ show (map funcName funs))
                 DefineSigsRec
                 (mapM fun2SMT funs)
-}

-- Translate a function declaration into a (possibly polymorphic)
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
        lhs = tComb (transOpName qn) (map TSVar vs)
    rhs <- exp2SMT (if isnd then Just lhs else Nothing) (simpExpr exp)
    return $
      Forall (map (\ (v,t) -> SV v (type2sort t))
                  (funcType2TypedVars vs texp))
             (if isnd then rhs else tEqu lhs rhs)

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
--- Translates a FlatCurry type expression into a corresponding SMT sort.
--- Type variables are translated into the sort `TVar` where a
--- type variable index is appended (`TVari`) in order to generate
--- a polymorphic sort (which will later be translated by the
--- SMT translator).
--- The types `TVar` and `Func` are defined in the SMT prelude
--- which is always loaded.
type2sort :: TypeExpr -> Sort
type2sort (TVar i) = SComb --"TVar" []
                           ("TVar" ++ show i) []
type2sort (TCons qc targs) =
  SComb (tcons2SMT qc) (map type2sort targs)
type2sort (FuncType dom ran) =
  SComb "Func" (map type2sort [dom,ran])
type2sort (ForallType _ te) = type2sort te
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
 | mn=="Prelude" = fromMaybe (if "is-" `isPrefixOf` fn then fn else tname)
                             (lookup fn primNames)
 | otherwise     = tname
 where
  tname = mn ++ "_" ++ encodeSpecialChars fn

--- Translates a (translated) SMT string back into qualified FlatCurry name.
--- Returns Nothing if it was not a qualified name.
untransOpName :: String -> Maybe QName
untransOpName s
 | "is-" `isPrefixOf` s
 = Nothing -- selectors are not a qualified name
 | otherwise
 = let (mn,ufn) = break (=='_') s
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
  getAllFuncs mods [] {-preloadedFuncDecls-} newfuns
 where
  getAllFuncs _       currfuncs [] = return (reverse currfuncs)
  getAllFuncs allmods currfuncs (newfun:newfuncs)
    | newfun `elem` excludedCurryOperations ||
      newfun `elem` map (pre . fst) primNames ||
      newfun `elem` map funcName currfuncs || isPrimOp newfun ||
      isTestPred newfun
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

  isTestPred (mn,fn) = mn == "Prelude" && "is-" `isPrefixOf` fn

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
  [Func (pre "null") 1 Public 
     (FuncType (fcList (TVar 0)) fcBool)
     (Rule [1] (Case Flex (Var 1)
                  [Branch (Pattern (pre "[]") [])   fcTrue,
                   Branch (Pattern (pre ":") [2,3]) fcFalse]))
  ]

--- Exclude character-related operations since characters are treated as
--- integers so that these operations are not required.
excludedCurryOperations :: [QName]
excludedCurryOperations = map pre ["chr", "ord"]

--- Returns the names of all functions occurring in the
--- body of a function declaration.
funcsOfFuncDecl :: FuncDecl -> [QName]
funcsOfFuncDecl fd =
  nub (trRule (\_ e -> funcsInExpr e) (\_ -> []) (funcRule fd))

------------------------------------------------------------------------------