{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms   #-}
module Common where

import Prelude hiding (print)

import Control.Monad.Except
import Data.Char
import Data.List

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

import qualified Text.Parsec as P
import qualified Text.Parsec.Pos as Pos
import Text.Parsec.Token
import Text.ParserCombinators.Parsec hiding (State, parse)
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Language

import System.IO.Error

import qualified Data.Map as Map

import Control.Monad.Identity (Identity, runIdentity)

import qualified PatternUnify.Tm as Tm

data Region =
  SourceRegion SourcePos
  | BuiltinRegion
  deriving (Eq, Ord, Show)

prettySource :: Region -> String
prettySource (SourceRegion pos) =
   prettyPos pos
prettySource s = "builtin:"

prettyPos pos = (sourceName pos) ++ ": " ++ (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos)

regionName BuiltinRegion = "builtin"
regionName (SourceRegion pos) = --TODO multiFile
  (show (sourceLine pos))
  ++ "_" ++ show (sourceColumn pos)

compactRegion :: Region -> String
compactRegion (SourceRegion pos) = (show $ sourceLine pos) ++ "," ++ (show $ sourceColumn pos)
compactRegion _ = "0,0"

data Located a = L {region :: Region, contents :: a}
  deriving (Eq, Ord, Show)

type LPParser = P.ParsecT String SourcePos Identity

startRegion = SourceRegion $ Pos.initialPos ""

catch = catchIOError

builtin x = L BuiltinRegion x

getRegion = SourceRegion `fmap` getPosition


simplyTyped = makeTokenParser (haskellStyle { identStart = letter {-<|> P.char '_'-},
                                              reservedNames = ["_", "match", "let", "assume", "putStrLn"] })





parseIO :: String -> LPParser a -> String -> IO (Maybe a)
parseIO f p x =
  let
    --doParse :: LPParser Int
    doParse = do
      whiteSpace simplyTyped
      x <- p
      eof
      return x
  in
    case runIdentity $ P.runParserT doParse (Pos.initialPos "") f x of
                  Left e  -> putStrLn (show e) >> return Nothing
                  Right r -> return (Just r)


parseSimple :: String -> LPParser a -> String -> Either [(Maybe SourcePos, String)] a
parseSimple fileName p x =
  let
    --doParse :: LPParser Int
    doParse = do
      whiteSpace simplyTyped
      x <- p
      eof
      return x
  in
    case runIdentity $ P.runParserT doParse (Pos.initialPos "") fileName x of
                  Left e  -> Left [(Just $ errorPos e, intercalate "\n" $ map messageString $ errorMessages e)]
                  Right r -> Right r

vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id


lambdaPi = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                           reservedNames = ["forall", "exists", "fst", "snd", "let", "assume", "putStrLn", "out"] })

parseStmt_ :: [String] -> LPParser (Stmt ITerm_ CTerm_)
parseStmt_ e =
      do
        reserved lambdaPi "let"
        x <- identifier lambdaPi
        reserved lambdaPi "="
        t <- parseITerm_ 0 e
        return (Let x t)
  <|> do
        reserved lambdaPi "assume"
        (xs, ts) <- parseBindings_ False []
        return (Assume (reverse (zip xs ts)))
  <|> do
        reserved lambdaPi "putStrLn"
        x <- stringLiteral lambdaPi
        return (PutStrLn x)
  <|> do
        reserved lambdaPi "out"
        x <- option "" (stringLiteral lambdaPi)
        return (Out x)
  <|> fmap Eval (parseITerm_ 0 e)

parseBindings_ :: Bool -> [String] -> LPParser ([String], [CTerm_])
parseBindings_ b e =
                   (let rec :: [String] -> [CTerm_] -> LPParser ([String], [CTerm_])
                        rec e ts =
                          do
                           (x,t) <- parens lambdaPi
                                      (do
                                         x <- identifier lambdaPi
                                         reserved lambdaPi "::"
                                         t <- parseCTerm_ 0 (if b then e else [])
                                         return (x,t))
                           (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                    in rec e [])
                   <|>
                   do  x <- identifier lambdaPi
                       reserved lambdaPi "::"
                       t <- parseCTerm_ 0 e
                       return (x : e, [t])

parseITerm_ :: Int -> [String] -> LPParser ITerm_
parseITerm_ 0 e = getRegion >>= \pos ->
      do
        reserved lambdaPi "forall"
        (fe,t:ts) <- parseBindings_ True e
        reserved lambdaPi "."
        t' <- parseCTerm_ 0 fe
        return (foldl (\ p t -> L pos $ Pi_ t (L pos $ Inf_ p)) (L pos $  Pi_ t t') ts)
  <|>
  do
    reserved lambdaPi "exists"
    (fe,t:ts) <- parseBindings_ True e
    reserved lambdaPi "."
    t' <- parseCTerm_ 0 fe
    return (foldl (\ p t -> L pos $ Sigma_ t (L pos $ Inf_ p)) (L pos $  Sigma_ t t') ts)
  <|>
  try
     (do
        t <- parseITerm_ 1 e
        rest (L pos $ Inf_ t) <|> return t)
  <|> try (do
        t <- parsePair_ e
        rest t)
  <|> do
          t <- parens lambdaPi (parseLam_ e)
          rest t
  where
    rest t =
      do
        pos <- getRegion
        reserved lambdaPi "->"
        t' <- parseCTerm_ 0 ([]:e)
        return (L pos $ Pi_ t t')
parseITerm_ 1 e = getRegion >>= \pos ->
  try
     (do
        t <- parseITerm_ 2 e
        rest (L pos $ Inf_ t) <|> return t)
  <|> try (do
        t <- parsePair_ e
        rest t)
  <|> do
        t <- parens lambdaPi (parseLam_ e)
        rest t
  where
    rest t =
      do
        pos <- getRegion
        reserved lambdaPi "::"
        t' <- parseCTerm_ 0 e
        return (L pos $ Ann_ t t')
parseITerm_ 2 e =
      do
        pos <- getRegion
        t <- parseITerm_ 3 e
        ts <- many (parseCTerm_ 3 e)
        let app x y = L pos (x :$: y)
        return (foldl app t ts)
parseITerm_ 3 e = getRegion >>= \pos ->
      do
        reserved lambdaPi "*"
        return $ L pos Star_
  <|> do
        reserved lambdaPi "_"
        return $ L pos $ Meta_ ("β_" ++ regionName pos)
  <|>
    do
        reserved lambdaPi "fst"
        pr <- parseITerm_ 3 e
        return (L pos $ Fst_ pr)
  <|>
    do
        reserved lambdaPi "snd"
        pr <- parseITerm_ 3 e
        return (L pos $ Snd_ pr)
  <|> do
        n <- natural lambdaPi
        return (toNat_ pos n)
  <|> do
        x <- identifier lambdaPi
        case findIndex (== x) e of
          Just n  -> return (L pos $ Bound_ n)
          Nothing -> return (L pos $ Free_ (Global x))
  <|> parens lambdaPi (parseITerm_ 0 e)
parseITerm_ _ _ = undefined

parseCTerm_ :: Int -> [String] -> LPParser CTerm_
parseCTerm_ 0 e = getRegion >>= \pos ->
      parseLam_ e
    <|>
      try (parsePair_ e)
    <|> fmap (\x -> L pos (Inf_ x)) (parseITerm_ 0 e)
parseCTerm_ p e =  getRegion >>= \pos ->
      try (parsePair_ e)
  <|> try (parens lambdaPi (parseLam_ e))
  <|> fmap (L pos . Inf_) (parseITerm_ p e)


parseLam_ :: [String] -> LPParser CTerm_
parseLam_ e =
      do
         pos <- getRegion
         let mkLam x = L pos (Lam_ x)
         reservedOp lambdaPi "\\"
         xs <- many1 (identifier lambdaPi)
         reservedOp lambdaPi "->"
         t <- parseCTerm_ 0 (reverse xs ++ e)
         --  reserved lambdaPi "."
         return (iterate mkLam t !! length xs)

parsePair_ :: [String] -> LPParser CTerm_
parsePair_ e = parens lambdaPi $
      do
         pos <- getRegion
         --reservedOp lambdaPi "<"
         s <- parseCTerm_ 0 e
         reservedOp lambdaPi ","
         t <- parseCTerm_ 0 e
         --reservedOp lambdaPi ">"
         return $ L pos $ Pair_ s t


toNat_ :: Region -> Integer -> ITerm_
toNat_ r n = L r $ Ann_ (toNat_' r n) (L r $ Inf_ $ L r Nat_)

toNat_' :: Region -> Integer -> CTerm_
toNat_' r 0  = L r Zero_
toNat_' r n  =  L r $ Succ_ (toNat_' r (n - 1))

locFree :: Name -> ITerm_
locFree x = builtin $ Free_ x

globalApp :: ITerm_ -> CTerm_ -> Located ITerm_'
globalApp x y = builtin $ x :$: y

iPrint_ :: Int -> Int -> ITerm_ -> Doc
iPrint_ p ii (L _ it) = iPrint_' p ii it
  where
    iPrint_' p ii (Ann_ c ty)       =  parensIf (p > 1) (cPrint_ 2 ii c <> text " :: " <> cPrint_ 0 ii ty)
    iPrint_' p ii Star_             =  text "*"
    iPrint_' p ii (Pi_ d (L _ (Inf_ (L _ (Pi_ d' r)))))
                                   =  parensIf (p > 0) (nestedForall_ (ii + 2) [(ii + 1, d'), (ii, d)] r)
    iPrint_' p ii (Pi_ d r)         =  parensIf (p > 0) (sep [text "forall " <>
      parensIf True (text (vars !! ii) <> text " :: " <> cPrint_ 0 ii d )
      <> text " .", cPrint_ 0 (ii + 1) r])
    iPrint_' p ii (Sigma_ d r)         =  parensIf (p > 0) (sep [text "exists " <>
      parensIf True (text (vars !! ii) <> text " :: " <> cPrint_ 0 ii d )
      <> text " .", cPrint_ 0 (ii + 1) r])
    iPrint_' p ii (Bound_ k)        =  text (vars !! (ii - k - 1))
    iPrint_' p ii (Free_ (Global s))=  text s
    iPrint_' p ii (i :$: c)         =  parensIf (p > 2) (sep [iPrint_ 2 ii i, nest 2 (cPrint_ 3 ii c)])
    iPrint_' p ii Nat_              =  text "Nat"
    iPrint_' p ii (NatElim_ m z s n)=  iPrint_ p ii (locFree (Global "natElim") `globalApp` m `globalApp` z `globalApp` s `globalApp` n)
    iPrint_' p ii (Vec_ a n)        =  iPrint_ p ii (locFree (Global "Vec") `globalApp` a `globalApp` n)
    iPrint_' p ii (VecElim_ a m mn mc n xs)
                                   =  iPrint_ p ii (locFree (Global "vecElim") `globalApp` a `globalApp` m `globalApp` mn `globalApp` mc `globalApp` n `globalApp` xs)
    iPrint_' p ii (Eq_ a x y)       =  iPrint_ p ii (locFree (Global "Eq") `globalApp` a `globalApp` x `globalApp` y)
    iPrint_' p ii (EqElim_ a m mr x y eq)
                                   =  iPrint_ p ii (locFree (Global "eqElim") `globalApp` a `globalApp` m `globalApp` mr `globalApp` x `globalApp` y `globalApp` eq)
    iPrint_' p ii (Fin_ n)          =  iPrint_ p ii (locFree (Global "Fin") `globalApp` n)
    iPrint_' p ii (FinElim_ m mz ms n f)
                                   =  iPrint_ p ii (locFree (Global "finElim") `globalApp` m `globalApp` mz `globalApp` ms `globalApp` n `globalApp` f)
    iPrint_' p ii (Fst_ pr)          =  text "fst" <> iPrint_ p ii pr
    iPrint_' p ii (Snd_ pr)          =  text "snd" <> iPrint_ p ii pr
    iPrint_' p ii x                 =  text ("[" ++ show x ++ "]")

cPrint_ :: Int -> Int -> CTerm_ -> Doc
cPrint_ p ii (L reg ct) = cPrint_' p ii ct
  where
    cPrint_' p ii (Inf_ i)    = iPrint_ p ii i
    cPrint_' p ii (Lam_ c)    = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint_ 0 (ii + 1) c)
    cPrint_' p ii (Pair_ h t)    = parensIf True ( cPrint_ p ii h <> text " , " <> cPrint_ 0 (ii + 1) t)
    cPrint_' p ii Zero_       = fromNat_ 0 ii (L reg Zero_)     --  text "Zero"
    cPrint_' p ii (Succ_ n)   = fromNat_ 0 ii (L reg $ Succ_ n) --  iPrint_ p ii (Free_ (Global "Succ") :$: n)
    cPrint_' p ii (Nil_ a)    = iPrint_ p ii (locFree (Global "Nil") `globalApp` a)
    cPrint_' p ii (Cons_ a n x xs) =
                               iPrint_ p ii (locFree (Global "Cons") `globalApp` a `globalApp` n `globalApp` x `globalApp` xs)
    cPrint_' p ii (Refl_ a x) = iPrint_ p ii (locFree (Global "Refl") `globalApp` a `globalApp` x)
    cPrint_' p ii (FZero_ n)  = iPrint_ p ii (locFree (Global "FZero") `globalApp` n)
    cPrint_' p ii (FSucc_ n f)= iPrint_ p ii (locFree (Global "FSucc") `globalApp` n `globalApp` f)

fromNat_ :: Int -> Int -> CTerm_ -> Doc
fromNat_ n ii (L _ Zero_) = int n
fromNat_ n ii (L _ (Succ_ k)) = fromNat_ (n + 1) ii k
fromNat_ n ii t = parensIf True (int n <> text " + " <> cPrint_ 0 ii t)

nestedForall_ :: Int -> [(Int, CTerm_)] -> CTerm_ -> Doc
nestedForall_ ii ds (L _ (Inf_ (L _ (Pi_ d r)))) = nestedForall_ (ii + 1) ((ii, d) : ds) r
nestedForall_ ii ds x                = sep [text "forall " <> sep [parensIf True (text (vars !! n) <> text " :: " <> cPrint_ 0 n d) | (n,d) <- reverse ds] <> text " .", cPrint_ 0 ii x]

data Stmt i tinf = Let String i           --  let x = t
                 | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                 | Eval i
                 | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                 | Out String             --  more lhs2TeX hacking, allow to print to files
  deriving (Show)

--  read-eval-print loop
readevalprint :: Interpreter i c v t tinf inf -> State v inf -> IO ()
readevalprint int state@(inter, out, ve, te) =
  let rec int state =
        do
          x <- catch
                 (if inter
                  then putStr (iprompt int ++ " ") >> (Just <$> getLine)
                  else fmap Just getLine)
                 (\_ -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->  rec int state
            Just x    ->
              do
                --when inter (addHistory x)
                c  <- interpretCommand x
                state' <- handleCommand int state c
                maybe (return ()) (rec int) state'
  in
    do
      --  welcome
      when inter $ putStrLn ("Interpreter for " ++ iname int ++ ".\n" ++
                             "Type :? for help.")
      --  enter loop
      rec int state

data Command = TypeOf String
             | Compile CompileForm
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

type NameEnv v = [(Name, v)]
type Ctx inf = [(Name, inf)]
type State v inf = (Bool, String, NameEnv v, Ctx inf)

--Returns value's type, value with metas filled in, and dictionary of solved meta values (for printing)
type TypeChecker =
  (NameEnv Tm.VAL, [(Name, Tm.VAL)]) -> ITerm_ -> Result (Type_, Tm.VAL, [(Region, Tm.VAL)])

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":type"]        "<expr>"  TypeOf         "print type of expression",
       Cmd [":browse"]      ""        (const Browse) "browse names in scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "load program from file",
       Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
       Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "List of commands:  Any command may be abbreviated to :c where\n" ++
     "c is the first character in the full name.\n\n" ++
     "<expr>                  evaluate expression\n" ++
     "let <var> = <expr>      define variable\n" ++
     "assume <var> :: <expr>  assume variable\n\n"
     ++
     unlines (map (\ (Cmd cs a _ d) -> let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) cs))
                                       in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)


interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             x   ->  do  putStrLn ("Ambiguous command, could be " ++ concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop
     else
       return (Compile (CompileInteractive x))

handleCommand :: Interpreter i c v t tinf inf -> State v inf -> Command -> IO (Maybe (State v inf))
handleCommand int state@(inter, out, ve, te) cmd
  =  case cmd of
       Quit   ->  when (not inter) (putStrLn "!@#$^&*") >> return Nothing
       Noop   ->  return (Just state)
       Help   ->  putStr (helpTxt commands) >> return (Just state)
       TypeOf x ->
                  do  x <- parseIO "<interactive>" (iiparse int) x
                      infResult <- maybe (return Nothing) (iinfer int ve te) x
                      let (t, _, _) =
                            case infResult of
                              Nothing -> (Nothing, Nothing, Nothing)
                              (Just (x,y,z)) -> (Just x, Just y, Just z)

                      maybe (return ()) (\u -> putStrLn (render (itprint int u))) t
                      return (Just state)
       Browse ->  do  putStr (unlines [ s | Global s <- reverse (nub (map fst te)) ])
                      return (Just state)
       Compile c ->
                  do  state <- case c of
                                 CompileInteractive s -> compilePhrase int state s
                                 CompileFile f        -> compileFile int state f
                      return (Just state)

compileFile :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compileFile int state@(inter, out, ve, te) f =
  do
    x <- readFile f
    stmts <- parseIO f (many (isparse int)) x
    maybe (return state) (foldM (handleStmt int) state) stmts



compilePhrase :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compilePhrase int state@(inter, out, ve, te) x =
  do
    x <- parseIO "<interactive>" (isparse int) x
    maybe (return state) (handleStmt int state) x

data Interpreter i c v t tinf inf =
  I { iname    :: String,
      iprompt  :: String,
      iitype   :: NameEnv v -> Ctx inf -> i -> Result (t, v, [(Region, v)]),
      iquote   :: v -> c,
      ieval    :: NameEnv v -> i -> v,
      ihastype :: t -> inf,
      icprint  :: c -> Doc,
      itprint  :: t -> Doc,
      ivprint  :: v -> Doc,
      iiparse  :: LPParser i,
      isparse  :: LPParser (Stmt i tinf),
      iassume  :: State v inf -> (String, tinf) -> IO (State v inf) }



lpte :: Ctx Tm.VAL
lpte =      [(Global "Zero", Tm.Nat),
             (Global "Succ", Tm.Nat Tm.--> Tm.Nat),
             (Global "Nat", Tm.SET),
             (Global "natElim", pi_ (Tm.Nat Tm.--> Tm.SET) "natT_m" (\ m ->
                               (m `Tm.app` Tm.Zero) Tm.--> (
                               (Tm.msType m) Tm.--> (
                               pi_ Tm.Nat "natT_n" (\ n -> m `Tm.app` (var n)))))),
             (Global "Nil", pi_ Tm.SET "a" (\ a -> Tm.Vec (var a) Tm.Zero)),
             (Global "Cons", pi_ Tm.SET "a" (\ a ->
                            pi_ Tm.Nat "n" (\ n ->
                            (var a) Tm.--> ((Tm.Vec (var a) (var n)) Tm.--> (Tm.Vec (var a) (Tm.Succ $ var n)))))),
             (Global "Vec", Tm.SET Tm.--> (Tm.Nat Tm.--> ( Tm.SET))),
             (Global "vecElim", pi_ Tm.SET "a" (\ a ->
                               pi_ (Tm.vmType a) "m" (\ m ->
                               (Tm.mnType a m) Tm.--> (
                               (Tm.mcType a m ) Tm.--> (
                               pi_ Tm.Nat "n" (\ n ->
                               pi_ (Tm.Vec (var a) (var n)) "xs" (\ xs -> Tm.vResultType m n xs))))))),
             (Global "Refl", pi_ Tm.SET "a" (\ a -> pi_ (var a) "x" (\ x ->
                            Tm.Eq (var a) (var x) (var x)))),
             (Global "Eq", pi_ Tm.SET "a" (\ a -> pi_ (var a) "x" (\ x -> pi_ (var a) "y" (\ y -> Tm.SET)))),
             (Global "eqElim", pi_ Tm.SET "a" (\ a ->
                              pi_ (Tm.eqmType $ var a) "m" (\ m ->
                              (Tm.eqmrType (a) m) Tm.--> (
                              pi_ (var a) "x" (\ x -> pi_ (var a) "y" (\ y ->
                              pi_ (Tm.Eq (var a) (var x) (var y)) "eq" (\ eq ->
                              Tm.eqResultType m x y eq))))))),
             (Global "FZero", pi_ Tm.Nat "n" (\ n -> Tm.Fin (Tm.Succ $ var n))),
             (Global "FSucc", pi_ Tm.Nat "n" (\ n -> (Tm.Fin $ var n) Tm.--> Tm.Fin (Tm.Succ $ var n))),
             (Global "Fin", Tm.Nat Tm.--> Tm.SET),
             (Global "finElim",
                pi_ (Tm.finmType) "finT_m" $ \m ->
                  (Tm.finmzType m) Tm.--> (Tm.finmsType m) Tm.-->
                  (Tm.finRetType m))
        ]



lam_ = Tm.lam_
pi_ = Tm.pi_
var = Tm.var


blam_ = builtin . Lam_
inf_ = builtin . Inf_
bbound_ = builtin . Bound_

lpve :: Ctx Tm.VAL
lpve =
     [(Global "Zero", Tm.Zero),
             (Global "Succ", lam_ "n" (\ n -> Tm.Succ $ var n)),
             (Global "Nat", Tm.Nat),
             (Global "natElim",
                lam_ "nat_m" $ \m ->
                lam_ "nat_mz" $ \mz ->
                lam_ "nat_ms" $ \ms ->
                lam_ "nat_k" $ \k ->
                  Tm.N (Tm.Var k Tm.Only) [Tm.NatElim (var m) (var mz) (var ms)]
                  ),
             (Global "Nil", lam_ "a" (\ a -> Tm.VNil $ var a)),
             (Global "Cons", lam_ "a" (\ a -> lam_ "n" (\ n -> lam_ "x" (\ x -> lam_ "xs" (\ xs ->
                            Tm.VCons (var a) (var n) (var x) (var xs)))))),
             (Global "Vec", lam_ "a" (\ a -> lam_ "n" (\ n -> Tm.Vec (var a) (var n)))),
             (Global "vecElim",
                lam_ "vec_a" $ \a ->
                lam_ "vec_m" $ \m ->
                lam_ "vec_mn" $ \mn ->
                lam_ "vec_mc" $ \mc ->
                lam_ "vec_k" $ \mk ->
                lam_ "vec_xs" $ \xs ->
                  Tm.N (Tm.Var xs Tm.Only) [Tm.VecElim (var a) (var m) (var mn) (var mc) (var mk)]),
             (Global "Refl", lam_ "a" (\ a -> lam_ "x" (\ x -> Tm.ERefl (var a) (var x)))),
             (Global "Eq", lam_ "a" (\ a -> lam_ "x" (\ x -> lam_ "y" (\ y -> Tm.Eq(var a) (var x) (var y))))),
             (Global "eqElim",
                lam_ "eq_a" $ \a ->
                lam_ "eq_m" $ \m ->
                lam_ "eq_mr" $ \mr ->
                lam_ "eq_x" $ \x ->
                lam_ "eq_y" $ \y ->
                lam_ "eq_eq" $ \eq ->
                Tm.N (Tm.Var eq Tm.Only) [Tm.VecElim (var a) (var m) (var mr) (var x) (var y)]),
             (Global "FZero", lam_ "n" (\ n -> Tm.FZero $ var n)),
             (Global "FSucc", lam_ "n" (\ n -> lam_ "f" (\ f -> Tm.FSucc (var n) (var f)))),
             (Global "Fin", lam_ "n" (\ n -> Tm.Fin $ var n)),
             (Global "finElim",
                lam_ "fin_m" $ \m ->
                  lam_ "fin_mz" $ \mz ->
                    lam_ "fin_ms" $ \ms ->
                      lam_ "fin_n" $ \n ->
                        Tm.lam_ "fin_fin" $ \fin ->
                          Tm.N (Tm.Var fin Tm.Only) [Tm.FinElim (var m) (var mz) (var ms) (var n)])
             ]


solvedMetasString int subs =
  "Solved metas:\n"
  ++ intercalate "\n " (flip map subs $ \(loc, val) ->
      "    " ++ compactRegion loc ++ " := " ++ (render $ ivprint int val))

makeOutText int i y v subs =
  if i == it then render (ivprint int v <> text " :: " <> itprint int y)
                           else render (text i <> text " :: " <> itprint int y)

iinfer :: Interpreter i c v t tinf inf -> NameEnv v -> Ctx inf -> i -> IO (Maybe (t, v, [(Region, v)]))
iinfer int d g t =
  case iitype int d g t of
    Left errs -> (forM errs $ \(pos, e) -> putStrLn ("ERROR: " ++ (maybe "<builtin>" prettyPos pos) ++ " " ++ e)) >> return Nothing
    Right v -> return (Just v)

handleStmt :: Interpreter i c v t tinf inf
              -> State v inf -> Stmt i tinf -> IO (State v inf)
handleStmt int state@(inter, out, ve, te) stmt =
  do
    case stmt of
        Assume ass -> foldM (iassume int) state ass
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (inter, f, ve, te)
  where
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      check int state i t
        (\ (y, v, subs) -> do
                       --  ugly, but we have limited space in the paper
                       --  usually, you'd want to have the bound identifier *and*
                       --  the result of evaluation
                       let outtext = makeOutText int i y v subs
                       putStrLn outtext
                       case subs of
                         [] -> return ()
                         _ -> do
                           putStrLn $ solvedMetasString int subs
                           return ()
                       unless (null out) (writeFile out (process outtext)))
        (\ (y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype int y) : te))

check :: Interpreter i c v t tinf inf -> State v inf -> String -> i
         -> ((t, v, [(Region, v)]) -> IO ()) -> ((t, v) -> State v inf) -> IO (State v inf)
check int state@(inter, out, ve, te) i t kp k =
                do
                  --  typecheck and evaluate
                  x <- iinfer int ve te t
                  case x of
                    Nothing  ->
                      do
                        --  putStrLn "type error"
                        return state
                    Just (y, newVal, subs)   ->
                      do
                        let v = ieval int ve t
                        kp (y, newVal, subs)
                        return (k (y, newVal))



it = "it"

process :: String -> String
process = unlines . map (\ x -> "< " ++ x) . lines

data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq)






type Result a = Either [(Maybe SourcePos, String)] a


type CTerm_ = Located CTerm_'

data CTerm_'
   =  Inf_  ITerm_
   |  Lam_  CTerm_
   |  Pair_  CTerm_ CTerm_

   |  Zero_
   |  Succ_ CTerm_

  |  Nil_ CTerm_
  |  Cons_ CTerm_ CTerm_ CTerm_ CTerm_

   |  Refl_ CTerm_ CTerm_

  |  FZero_ CTerm_
  |  FSucc_ CTerm_ CTerm_

  deriving (Show, Eq)

pattern Inf it <- L _ (Inf_ it)
pattern Lam ct <- L _ (Lam_ ct)


type ITerm_ = Located ITerm_'

data ITerm_'
   =  Ann_ CTerm_ CTerm_
   |  Star_
   |  Pi_ CTerm_ CTerm_
   |  Sigma_ CTerm_ CTerm_
   |  Bound_  Int
   |  Free_  Name
   |  ITerm_ :$: CTerm_

   | Meta_ String --Metavariables for implicits

   |  Nat_
   |  NatElim_ CTerm_ CTerm_ CTerm_ CTerm_

  |  Vec_ CTerm_ CTerm_
  |  VecElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_

   |  Eq_ CTerm_ CTerm_ CTerm_
   |  EqElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_

   |  Fin_ CTerm_
   |  FinElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Fst_ ITerm_
   |  Snd_ ITerm_

  deriving (Show, Eq)

pattern Ann t1 t2 <- L _ (Ann_ t1 t2)
pattern Star <- L _ Star_
pattern Pi t1 t2 <- L _ (Pi_ t1 t2)
pattern Bound i <- L _ (Bound_ i)
pattern Free nm <- L _ (Free_ nm)
pattern App it ct <- L _ (it :$: ct)


data Neutral_
   =  NFree_  Name
   |  NApp_  Neutral_ Tm.VAL

  |  NNatElim_ Tm.VAL Tm.VAL Tm.VAL Neutral_

  |  NVecElim_ Tm.VAL Tm.VAL Tm.VAL Tm.VAL Tm.VAL Neutral_

  |  NEqElim_ Tm.VAL Tm.VAL Tm.VAL Tm.VAL Tm.VAL Neutral_

  |  NFinElim_ Tm.VAL Tm.VAL Tm.VAL Tm.VAL Neutral_
  deriving (Show)

type Env_ = [Tm.VAL]


badVappError x y = error $ "Cannot apply value " ++ show x ++ " to value " ++ show y

vfree_ :: Name -> Tm.VAL
vfree_ n = error "TODO vFree" --VNeutral_ (NFree_ n)


iSubst_ :: Int -> ITerm_ -> ITerm_ -> ITerm_
iSubst_ ii i' (L reg it) = L reg $ iSubst_' ii i' it
  where
    iSubst_' _ _ (Meta_ x) = Meta_ x
    iSubst_' ii i'   (Ann_ c c')     =  Ann_ (cSubst_ ii i' c) (cSubst_ ii i' c')


    iSubst_' ii r  Star_           =  Star_
    iSubst_' ii r  (Pi_ ty ty')    =  Pi_  (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')
    iSubst_' ii r  (Sigma_ ty ty')    =  Sigma_  (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')

    iSubst_' ii (L _ isub) (Bound_ j)      =  if ii == j then isub else Bound_ j
    iSubst_' ii i' (Free_ y)       =  Free_ y
    iSubst_' ii i' (i :$: c)       =  iSubst_ ii i' i :$: cSubst_ ii i' c

    iSubst_' ii r  Nat_            =  Nat_
    iSubst_' ii r  (NatElim_ m mz ms n)
                                  =  NatElim_ (cSubst_ ii r m)
                                              (cSubst_ ii r mz) (cSubst_ ii r ms)
                                              (cSubst_ ii r ms)

    iSubst_' ii r  (Vec_ a n)      =  Vec_ (cSubst_ ii r a) (cSubst_ ii r n)
    iSubst_' ii r  (VecElim_ a m mn mc n xs)
                                  =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                              (cSubst_ ii r mn) (cSubst_ ii r mc)
                                              (cSubst_ ii r n) (cSubst_ ii r xs)

    iSubst_' ii r  (Eq_ a x y)     =  Eq_ (cSubst_ ii r a)
                                         (cSubst_ ii r x) (cSubst_ ii r y)
    iSubst_' ii r  (EqElim_ a m mr x y eq)
                                  =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                              (cSubst_ ii r mr) (cSubst_ ii r x)
                                              (cSubst_ ii r y) (cSubst_ ii r eq)

    iSubst_' ii r  (Fin_ n)        =  Fin_ (cSubst_ ii r n)
    iSubst_' ii r  (FinElim_ m mz ms n f)
                                  =  FinElim_ (cSubst_ ii r m)
                                              (cSubst_ ii r mz) (cSubst_ ii r ms)
                                              (cSubst_ ii r n) (cSubst_ ii r f)

    iSubst_' ii r  (Fst_ pr)        =  Fst_ (iSubst_ ii r pr)
    iSubst_' ii r  (Snd_ pr)        =  Snd_ (iSubst_ ii r pr)

cSubst_ :: Int -> ITerm_ -> CTerm_ -> CTerm_
cSubst_ ii i' (L reg ct) = L reg $ cSubst_' ii i' ct
  where
    cSubst_' ii i' (Inf_ i)      =  Inf_ (iSubst_ ii i' i)
    cSubst_' ii i' (Lam_ c)      =  Lam_ (cSubst_ (ii + 1) i' c)
    cSubst_' ii i' (Pair_ x y)      =  Pair_ (cSubst_ ii i' x) (cSubst_ ii i' y)

    cSubst_' ii r  Zero_         =  Zero_
    cSubst_' ii r  (Succ_ n)     =  Succ_ (cSubst_ ii r n)

    cSubst_' ii r  (Nil_ a)      =  Nil_ (cSubst_ ii r a)
    cSubst_' ii r  (Cons_ a n x xs)
                                =  Cons_ (cSubst_ ii r a) (cSubst_ ii r x)
                                         (cSubst_ ii r x) (cSubst_ ii r xs)

    cSubst_' ii r  (Refl_ a x)   =  Refl_ (cSubst_ ii r a) (cSubst_ ii r x)

    cSubst_' ii r  (FZero_ n)    =  FZero_ (cSubst_ ii r n)
    cSubst_' ii r  (FSucc_ n k)  =  FSucc_ (cSubst_ ii r n) (cSubst_ ii r k)


boundfree_ :: Int -> Name -> ITerm_
boundfree_ ii (Quote k)     =  builtin $ Bound_ ((ii - k - 1) `max` 0)
boundfree_ ii x             =  builtin $ Free_ x

instance Show (Tm.VAL -> Tm.VAL) where
  show f = error "TODO show fn" -- "<<" ++ (show $ quote0_ $ VLam_ f) ++ ">>"


type Type_     =  Tm.VAL
