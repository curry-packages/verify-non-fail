module Verify.WithSMT
 where

import Control.Monad      ( unless, when )
import Data.List          ( find, isPrefixOf, nub, partition, union )
import Data.Maybe         ( catMaybes, fromMaybe, isJust )
import Numeric            ( readHex )
import System.CPUTime     ( getCPUTime )

import FlatCurry.Goodies
import FlatCurry.Names
import FlatCurry.Print
import FlatCurry.Simplify
import FlatCurry.Types
import System.FilePath    ( (</>) )
import System.IOExts      ( evalCmd )

import Verify.ESMT hiding ( Let )
import Verify.Helpers
import Verify.Options
import PackageConfig      ( getPackagePath )

------------------------------------------------------------------------------
-- Calls the SMT solver to check whether an assertion implies some
-- property (represented as FlatCurry expressions).
-- If the implication is `False`, the unsatisfiability of the assertion
-- is checked.
checkImplicationWithSMT :: Options -> QName -> String -> [FuncDecl]
                        -> [(Int,TypeExpr)] -> Expr -> Expr -> IO (Maybe Bool)
checkImplicationWithSMT opts qf scripttitle fdecls vartypes
                        assertionexp impexp = do
  maybe (transExpError assertionexp)
        (\assertion ->
           maybe (transExpError impexp)
                 (checkImplicationWithSMT' opts qf scripttitle fdecls vartypes
                                           assertion)
                 (exp2SMT (simpExpr impexp)))
        (exp2SMT (simpExpr assertionexp))
 where
  transExpError e = do putStrLn $ "Cannot translate expression:\n" ++ showExp e
                       return Nothing


checkImplicationWithSMT' :: Options -> QName -> String -> [FuncDecl]
                         -> [(Int,TypeExpr)] -> Term -> Term -> IO (Maybe Bool)
checkImplicationWithSMT' opts qf scripttitle fdecls vartypes assertion
                         imp = flip catch (\_ -> return Nothing) $ do
  let (pretypes,usertypes) =
         partition ((== "Prelude") . fst)
                   (foldr union [] (map (tconsOfTypeExpr . snd) vartypes))
  let allsyms = catMaybes
                  (map (\n -> maybe Nothing Just (untransOpName n))
                       (map qidName
                         (allQIdsOfTerm (tConj [assertion, imp]))))
  unless (null allsyms) $ printWhenIntermediate opts $
    "Translating operations into SMT: " ++ unwords (map showQName allsyms)
  smtfuncs <- funcs2SMT fdecls allsyms
  let decls = map (maybe (error "Internal error: some datatype not found!") id)
                  [] --(map (tdeclOf vst) usertypes)
      smt   = --concatMap preludeType2SMT (map snd pretypes) ++
              [ EmptyLine ] ++
              (if null decls
                 then []
                 else [ Comment "User-defined datatypes:" ] ++
                      []) ++ -- map tdecl2SMT decls) ++
              [ EmptyLine, smtfuncs, EmptyLine
              , Comment "Free variables:" ] ++
              map typedVar2SMT vartypes ++
              [ EmptyLine
              , Comment "Boolean formula of assertion (known properties):"
              , sAssert assertion, EmptyLine
              --, Comment "Bindings of implication:"
              --, sAssert impbindings, EmptyLine
              , Comment "Assert negated implication:"
              , sAssert (tNot imp), EmptyLine
              , Comment "check satisfiability:"
              , CheckSat
              , Comment "if unsat, the implication is valid"
              ]
  --putStrLn $ "SMT commands as Curry term:\n" ++ show smt
  smtprelude <- if all ((`elem` ["Int","Float","Bool", "Char"]) . snd) pretypes 
                  then return ""
                  else do pp <- getPackagePath
                          readFile (pp </> "include" </> "Prelude.smt")
  let scripttitle' = map (\c -> if c == '\n' then ' ' else c) scripttitle
  let smtinput = "; " ++ scripttitle' ++ "\n\n" ++ smtprelude ++ showSMT smt
  printWhenDetails opts $ "SMT SCRIPT:\n" ++ showWithLineNums smtinput
  when (optStoreSMT opts) $ do
    ctime <- getCPUTime
    let outfile = "SMT-" ++ transOpName qf ++ "-" ++ show ctime ++ ".smt"
        execcmt = "; Run with: z3 -smt2 -T:5 " ++ outfile ++ "\n\n"
    writeFile outfile (execcmt ++ smtinput)
  printWhenDetails opts $ "CALLING Z3 (with options: -smt2 -T:5)..."
  (ecode,out,err) <- evalCmd "z3" ["-smt2", "-in", "-T:5"] smtinput
  when (ecode>0) $ do
    printWhenDetails opts $ "EXIT CODE: " ++ show ecode
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
funcs2SMT :: [FuncDecl] -> [QName] -> IO Command
funcs2SMT allfuncs qns = do
  -- get all relevant functions but exclude character related operations:
  funs <- getAllFunctions allfuncs (map pre ["chr", "ord"]) (nub qns)
  return $ maybe (Comment $ "ERROR when translating " ++ show (map funcName funs))
                 DefineSigsRec
                 (mapM fun2SMT funs)
  --return $ Comment (show (map funcName funs))

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
    let lhs = tComb (transOpName qn) (map TSVar vs)
    rhs <- exp2SMT exp
    return $
      Forall (map (\ (v,t) -> SV v (type2sort t))
                  (funcType2TypedVars vs texp))
             (tEqu lhs rhs)


-- Translates a (Boolean) FlatCurry expression into an SMT expression.
exp2SMT :: Expr -> Maybe Term
exp2SMT exp = case exp of
  Var i          -> Just $ TSVar i
  Lit l          -> Just $ lit2SMT l
  Comb _ qf args -> do targs <- mapM exp2SMT args
                       return $ if qf `elem` map pre ["chr","ord"] &&
                                   length targs == 1
                                  then head targs -- characters are integers
                                  else tComb (transOpName qf) targs
  Case _ _ _  -> Nothing --error $ "exp2SMT: Case"
  Let  _ _    -> Nothing --error "exp2SMT: Let"
  Free _ _    -> Nothing --error "exp2SMT: Free"
  Typed e _   -> exp2SMT e
  Or    e1 e2 -> do t1 <- exp2SMT e1
                    t2 <- exp2SMT e2
                    return $ tDisj [t1,t2]

--- Translates a literal into an SMT expression.
--- We represent character as ints.
lit2SMT :: Literal -> Term
lit2SMT (Intc i)   = TConst (TInt i)
lit2SMT (Floatc f) = TConst (TFloat f)
lit2SMT (Charc c)  = TConst (TInt (ord c))

----------------------------------------------------------------------------
--- Translates a FlatCurry type expression into a corresponding SMT sort.
--- If the first argument is null, then type variables are
--- translated into the sort `TVar`. If the second argument is true,
--- the type variable index is appended (`TVari`) in order to generate
--- a polymorphic sort (which will later be translated by the
--- SMT translator).
--- If the first argument is not null, we are in the translation
--- of the types of selector operations and the first argument
--- contains the currently defined data types. In this case, type variables
--- are translated into  `Ti`, but further nesting of the defined data types
--- are not allowed (since this is not supported by SMT).
--- The types `TVar` and `Func` are defined in the SMT prelude
--- which is always loaded.
type2sort :: TypeExpr -> Sort
type2sort (TVar _) = SComb "TVar" []
type2sort (TCons qc targs) =
  SComb (tcons2SMT qc) (map type2sort targs)
type2sort (FuncType dom ran) =
  SComb "Func" (map type2sort [dom,ran])
type2sort (ForallType _ _) =
  error "Veriy.WithSMT.type2SMT: cannot translate ForallType"

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
  ] ++
  map (\i -> ('(' : take (i-1) (repeat ',') ++ ")", "Tuple" ++ show i)) [3..15]

------------------------------------------------------------------------------
--- Extract all user-defined FlatCurry functions that might be called
--- by a given list of function names provided as the last argument.
--- The first argument is the list of all function declarations.
--- The second argument is a list of function names that will be excluded
--- (together with the functions called by them).
getAllFunctions :: [FuncDecl] -> [QName] -> [QName] -> IO [FuncDecl]
getAllFunctions allfuncs excluded = getAllFuncs []
 where
  getAllFuncs currfuncs [] = return (reverse currfuncs)
  getAllFuncs currfuncs (newfun:newfuncs)
    | newfun `elem` map (pre . fst) primNames ++ map funcName currfuncs
      || isPrimOp newfun
    = getAllFuncs currfuncs newfuncs
    | otherwise
    = maybe (error $ "getAllFunctions: " ++ show newfun ++ " not found!")
            (\fdecl -> getAllFuncs (fdecl : currfuncs)
                         (newfuncs ++
                          filter (`notElem` excluded) (funcsOfFuncDecl fdecl)))
            (find (\fd -> funcName fd == newfun) allfuncs)

--- Returns the names of all functions occurring in the
--- body of a function declaration.
funcsOfFuncDecl :: FuncDecl -> [QName]
funcsOfFuncDecl fd =
  nub (trRule (\_ e -> funcsInExpr e) (\_ -> []) (funcRule fd))

------------------------------------------------------------------------------

