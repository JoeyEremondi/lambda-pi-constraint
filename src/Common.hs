{-# LANGUAGE FlexibleInstances, PatternSynonyms #-}
module Common where

import           Prelude                                hiding (print)

import           Control.Monad.Error
import           Data.Char
import           Data.List

import           Text.PrettyPrint.HughesPJ              hiding (parens)
import qualified Text.PrettyPrint.HughesPJ              as PP

import qualified Text.Parsec                            as P
import qualified Text.Parsec.Pos                        as Pos
import           Text.Parsec.Token
import           Text.ParserCombinators.Parsec          hiding (State, parse)
import           Text.ParserCombinators.Parsec.Language

import           System.Console.Readline
import           System.IO                              hiding (print)

import           System.IO.Error

import           Control.Monad.Identity                 (Identity, runIdentity)
import qualified Control.Monad.State                    as State

import Unbound.LocallyNameless (s2n)
import qualified PatternUnify.Tm as Tm

data Region =
  SourceRegion SourcePos
  | BuiltinRegion
  deriving (Eq, Ord, Show)

prettySource :: Region -> String
prettySource (SourceRegion pos) =
   (show $ sourceLine pos) ++ ":" ++ (show $ sourceColumn pos)
prettySource s = "builtin:"

regionName BuiltinRegion = "builtin"
regionName (SourceRegion pos) = --TODO multiFile
  "β_" ++ (show (sourceColumn pos))
  ++ "_" ++ show (sourceLine pos)

data Located a = L {region :: Region, contents :: a}
  deriving (Eq, Ord, Show)

type LPParser = P.ParsecT String SourcePos Identity

startRegion = SourceRegion $ Pos.initialPos ""

catch = catchIOError

builtin x = L BuiltinRegion x

getRegion = SourceRegion `fmap` getPosition


putstrln x = putStrLn x

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


vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id


lambdaPi = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                           reservedNames = ["forall", "let", "assume", "putStrLn", "out"] })

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
  try
     (do
        t <- parseITerm_ 1 e
        rest (L pos $ Inf_ t) <|> return t)
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
        return $ L pos $ Meta_ (regionName pos)
  <|> do
        n <- natural lambdaPi
        return (toNat_ pos n)
  <|> do
        x <- identifier lambdaPi
        case findIndex (== x) e of
          Just n  -> return (L pos $ Bound_ n)
          Nothing -> return (L pos $ Free_ (Global x))
  <|> parens lambdaPi (parseITerm_ 0 e)

parseCTerm_ :: Int -> [String] -> LPParser CTerm_
parseCTerm_ 0 e = getRegion >>= \pos ->
      parseLam_ e
    <|> fmap (\x -> L pos (Inf_ x)) (parseITerm_ 0 e)
parseCTerm_ p e =  getRegion >>= \pos ->
      try (parens lambdaPi (parseLam_ e))
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

toNat_ :: Region -> Integer -> ITerm_
toNat_ r n = L r $ Ann_ (toNat_' r n) (L r $ Inf_ $ L r Nat_)

toNat_' :: Region -> Integer -> CTerm_
toNat_' r 0  = L r Zero_
toNat_' r n  =  L r $ Succ_ (toNat_' r (n - 1))

locFree :: Name -> ITerm_
locFree x = builtin $ Free_ x

--globalApp :: ITerm_ -> ITerm_ -> ITerm_
globalApp x y = builtin $ x :$: y

iPrint_ :: Int -> Int -> ITerm_ -> Doc
iPrint_ p ii (L _ it) = iPrint_' p ii it
  where
    iPrint_' p ii (Ann_ c ty)       =  parensIf (p > 1) (cPrint_ 2 ii c <> text " :: " <> cPrint_ 0 ii ty)
    iPrint_' p ii Star_             =  text "*"
    iPrint_' p ii (Pi_ d (L _ (Inf_ (L _ (Pi_ d' r)))))
                                   =  parensIf (p > 0) (nestedForall_ (ii + 2) [(ii + 1, d'), (ii, d)] r)
    iPrint_' p ii (Pi_ d r)         =  parensIf (p > 0) (sep [text "forall " <> text (vars !! ii) <> text " :: " <> cPrint_ 0 ii d <> text " .", cPrint_ 0 (ii + 1) r])
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
    iPrint_' p ii x                 =  text ("[" ++ show x ++ "]")

cPrint_ :: Int -> Int -> CTerm_ -> Doc
cPrint_ p ii (L reg ct) = cPrint_' p ii ct
  where
    cPrint_' p ii (Inf_ i)    = iPrint_ p ii i
    cPrint_' p ii (Lam_ c)    = parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint_ 0 (ii + 1) c)
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
                  then readline (iprompt int)
                  else fmap Just getLine)
                 (\_ -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->  rec int state
            Just x    ->
              do
                when inter (addHistory x)
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

type TypeChecker = (NameEnv Tm.VAL, [(Name, Tm.VAL)]) -> ITerm_ -> Result Type_

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
                      t <- maybe (return Nothing) (iinfer int ve te) x
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
      iitype   :: NameEnv v -> Ctx inf -> i -> Result t,
      iquote   :: v -> c,
      ieval    :: NameEnv v -> i -> v,
      ihastype :: t -> inf,
      icprint  :: c -> Doc,
      itprint  :: t -> Doc,
      iiparse  :: LPParser i,
      isparse  :: LPParser (Stmt i tinf),
      iassume  :: State v inf -> (String, tinf) -> IO (State v inf) }



lp :: TypeChecker -> Interpreter ITerm_ CTerm_ Value_ Value_ CTerm_ Value_
lp checker = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \ v c -> checker (v, c),
         iquote = quote0_,
         ieval = \ e x -> iEval_ x (e, []),
         ihastype = id,
         icprint = cPrint_ 0 0,
         itprint = cPrint_ 0 0 . quote0_,
         iiparse = parseITerm_ 0 [],
         isparse = parseStmt_ [],
         iassume = \ s (x, t) -> lpassume checker s x t }

--TODO put this back
lpte :: Ctx Tm.VAL
--lpte = --[(Global "Nat", VStar_)]
lpte =      [(Global "Zero", Tm.Nat),
             (Global "Succ", Tm.Nat Tm.--> Tm.Nat),
             (Global "Nat", Tm.SET),
             (Global "natElim", VPi_ (VPi_ VNat_ (\ _ -> VStar_)) (\ m ->
                               VPi_ (m `vapp_` VZero_) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ k -> VPi_ (m `vapp_` k) (\ _ -> (m `vapp_` (VSucc_ k))))) ( \ _ ->
                               VPi_ VNat_ (\ n -> m `vapp_` n))))),
             (Global "Nil", VPi_ VStar_ (\ a -> VVec_ a VZero_)),
             (Global "Cons", VPi_ VStar_ (\ a ->
                            VPi_ VNat_ (\ n ->
                            VPi_ a (\ _ -> VPi_ (VVec_ a n) (\ _ -> VVec_ a (VSucc_ n)))))),
             (Global "Vec", VPi_ VStar_ (\ _ -> VPi_ VNat_ (\ _ -> VStar_))),
             (Global "vecElim", VPi_ VStar_ (\ a ->
                               VPi_ (VPi_ VNat_ (\ n -> VPi_ (VVec_ a n) (\ _ -> VStar_))) (\ m ->
                               VPi_ (m `vapp_` VZero_ `vapp_` (VNil_ a)) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ n ->
                                     VPi_ a (\ x ->
                                     VPi_ (VVec_ a n) (\ xs ->
                                     VPi_ (m `vapp_` n `vapp_` xs) (\ _ ->
                                     m `vapp_` VSucc_ n `vapp_` VCons_ a n x xs))))) (\ _ ->
                               VPi_ VNat_ (\ n ->
                               VPi_ (VVec_ a n) (\ xs -> m `vapp_` n `vapp_` xs))))))),
             (Global "Refl", VPi_ VStar_ (\ a -> VPi_ a (\ x ->
                            VEq_ a x x))),
             (Global "Eq", VPi_ VStar_ (\ a -> VPi_ a (\ x -> VPi_ a (\ y -> VStar_)))),
             (Global "eqElim", VPi_ VStar_ (\ a ->
                              VPi_ (VPi_ a (\ x -> VPi_ a (\ y -> VPi_ (VEq_ a x y) (\ _ -> VStar_)))) (\ m ->
                              VPi_ (VPi_ a (\ x -> m `vapp_` x `vapp_` x `vapp_` VRefl_ a x)) (\ _ ->
                              VPi_ a (\ x -> VPi_ a (\ y ->
                              VPi_ (VEq_ a x y) (\ eq ->
                              m `vapp_` x `vapp_` y `vapp_` eq))))))),
             (Global "FZero", VPi_ VNat_ (\ n -> VFin_ (VSucc_ n))),
             (Global "FSucc", VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f ->
                             VFin_ (VSucc_ n)))),
             (Global "Fin", VPi_ VNat_ (\ n -> VStar_)),
             (Global "finElim", VPi_ (VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ _ -> VStar_))) (\ m ->
                               VPi_ (VPi_ VNat_ (\ n -> m `vapp_` (VSucc_ n) `vapp_` (VFZero_ n))) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f -> VPi_ (m `vapp_` n `vapp_` f) (\ _ -> m `vapp_` (VSucc_ n) `vapp_` (VFSucc_ n f))))) (\ _ ->
                               VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f ->
                               m `vapp_` n `vapp_` f))))))]


lam_ s f = Tm.lam (s2n s) (f $ Tm.vv s)
inf_ = error "TODO inf_"

lpve :: Ctx Tm.VAL
lpve = -- [(Global "Nat", VNat_)]
     [(Global "Zero", Tm.Zero),
             (Global "Succ", lam_ "n" (\ n -> Tm.Succ n)),
             (Global "Nat", Tm.Nat),
             (Global "natElim",
                lam_ "m" $ \m ->
                lam_ "mz" $ \mz ->
                lam_ "ms" $ \ms ->
                lam_ "k" $ \k ->
                  k Tm.%% (Tm.NatElim m mz ms)
                  ),
             (Global "Nil", lam_ "a" (\ a -> Tm.VNil a)),
             (Global "Cons", lam_ "a" (\ a -> lam_ "n" (\ n -> lam_ "x" (\ x -> lam_ "xs" (\ xs ->
                            Tm.VCons a n x xs))))),
             (Global "Vec", lam_ "a" (\ a -> lam_ "n" (\ n -> Tm.Vec a n))),
             (Global "vecElim",
                lam_ "a" $ \a ->
                lam_ "m" $ \m ->
                lam_ "mn" $ \mn ->
                lam_ "mc" $ \mc ->
                lam_ "k" $ \mk ->
                lam_ "xs" $ \xs ->
                  xs Tm.%% Tm.VecElim a m mn mc mk),
             (Global "Refl", lam_ "a" (\ a -> lam_ "x" (\ x -> Tm.ERefl a x))),
             (Global "Eq", lam_ "a" (\ a -> lam_ "x" (\ x -> lam_ "y" (\ y -> Tm.Eq a x y)))),
             (Global "eqElim",
                lam_ "a" $ \a ->
                lam_ "m" $ \m ->
                lam_ "mr" $ \mr ->
                lam_ "x" $ \x ->
                lam_ "y" $ \y ->
                lam_ "eq" $ \eq ->
                eq Tm.%% Tm.EqElim a m mr x y)
             --(Global "FZero", VLam_ (\ n -> VFZero_ n)),
             --(Global "FSucc", VLam_ (\ n -> VLam_ (\ f -> VFSucc_ n f))),
             --(Global "Fin", VLam_ (\ n -> VFin_ n)),
             --(Global "finElim", cEval_ (lam_ (lam_ (lam_ (lam_ (lam_ (inf_ (FinElim_ (inf_ (Bound_ 4)) (inf_ (Bound_ 3)) (inf_ (Bound_ 2)) (inf_ (Bound_ 1)) (inf_ (Bound_ 0))))))))) ([],[]))
             ]


repLP :: TypeChecker -> Bool -> IO ()
repLP checker b = readevalprint (lp checker) (b, [], lpve, lpte)


iinfer int d g t =
  case iitype int d g t of
    Left e -> putStrLn e >> return Nothing
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
        (\ (y, v) -> do
                       --  ugly, but we have limited space in the paper
                       --  usually, you'd want to have the bound identifier *and*
                       --  the result of evaluation
                       let outtext = if i == it then render (icprint int (iquote int v) <> text " :: " <> itprint int y)
                                                else render (text i <> text " :: " <> itprint int y)
                       putStrLn outtext
                       unless (null out) (writeFile out (process outtext)))
        (\ (y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype int y) : te))

check :: Interpreter i c v t tinf inf -> State v inf -> String -> i
         -> ((t, v) -> IO ()) -> ((t, v) -> State v inf) -> IO (State v inf)
check int state@(inter, out, ve, te) i t kp k =
                do
                  --  typecheck and evaluate
                  x <- iinfer int ve te t
                  case x of
                    Nothing  ->
                      do
                        --  putStrLn "type error"
                        return state
                    Just y   ->
                      do
                        let v = ieval int ve t
                        kp (y, v)
                        return (k (y, v))

stassume state@(inter, out, ve, te) x t = return (inter, out, ve, (Global x, t) : te)
lpassume checker state@(inter, out, ve, te) x t =
  check (lp checker) state x (builtin $ Ann_ t (builtin $ Inf_ $ builtin $ Star_))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))


it = "it"

process :: String -> String
process = unlines . map (\ x -> "< " ++ x) . lines

data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq)






type Result a = Either String a


type CTerm_ = Located CTerm_'

data CTerm_'
   =  Inf_  ITerm_
   |  Lam_  CTerm_

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

  deriving (Show, Eq)

pattern Ann t1 t2 <- L _ (Ann_ t1 t2)
pattern Star <- L _ Star_
pattern Pi t1 t2 <- L _ (Pi_ t1 t2)
pattern Bound i <- L _ (Bound_ i)
pattern Free nm <- L _ (Free_ nm)
pattern App it ct <- L _ (it :$: ct)

data Value_
   =  VLam_  (Value_ -> Value_)
   |  VStar_
   |  VPi_ Value_ (Value_ -> Value_)
   |  VNeutral_ Neutral_

  |  VNat_
  |  VZero_
  |  VSucc_ Value_

  |  VNil_ Value_
  |  VCons_ Value_ Value_ Value_ Value_
  |  VVec_ Value_ Value_

  |  VEq_ Value_ Value_ Value_
  |  VRefl_ Value_ Value_

  |  VFZero_ Value_
  |  VFSucc_ Value_ Value_
  |  VFin_ Value_
  deriving (Show)

data Neutral_
   =  NFree_  Name
   |  NApp_  Neutral_ Value_

  |  NNatElim_ Value_ Value_ Value_ Neutral_

  |  NVecElim_ Value_ Value_ Value_ Value_ Value_ Neutral_

  |  NEqElim_ Value_ Value_ Value_ Value_ Value_ Neutral_

  |  NFinElim_ Value_ Value_ Value_ Value_ Neutral_
  deriving (Show)

type Env_ = [Value_]

vapp_ :: Value_ -> Value_ -> Value_
vapp_ (VLam_ f)      v  =  f v
vapp_ (VNeutral_ n)  v  =  VNeutral_ (NApp_ n v)
vapp_ x y = badVappError x y

badVappError x y = error $ "Cannot apply value " ++ show x ++ " to value " ++ show y

vfree_ :: Name -> Value_
vfree_ n = VNeutral_ (NFree_ n)

cEval_ :: CTerm_ -> (NameEnv Value_,Env_) -> Value_
cEval_ (L _ ct) d = cEval_' ct d
  where
    cEval_' (Inf_  ii)    d  =  iEval_ ii d
    cEval_' (Lam_  c)     d  =  VLam_ (\ x -> cEval_ c (((\(e, d) -> (e,  (x : d))) d)))

    cEval_' Zero_      d  = VZero_
    cEval_' (Succ_ k)  d  = VSucc_ (cEval_ k d)

    cEval_' (Nil_ a)          d  =  VNil_ (cEval_ a d)
    cEval_' (Cons_ a n x xs)  d  =  VCons_  (cEval_ a d) (cEval_ n d)
                                           (cEval_ x d) (cEval_ xs d)

    cEval_' (Refl_ a x)       d  =  VRefl_ (cEval_ a d) (cEval_ x d)

    cEval_' (FZero_ n)    d  =  VFZero_ (cEval_ n d)
    cEval_' (FSucc_ n f)  d  =  VFSucc_ (cEval_ n d) (cEval_ f d)

iEval_ :: ITerm_ -> (NameEnv Value_,Env_) -> Value_
iEval_ (L _ it) d = iEval_' it d
  where
    iEval_' (Ann_  c _)       d  =  cEval_ c d

    iEval_' Star_           d  =  VStar_
    iEval_' (Pi_ ty ty')    d  =  VPi_ (cEval_ ty d) (\ x -> cEval_ ty' (((\(e, d) -> (e,  (x : d))) d)))

    iEval_' (Free_  x)      d  =  case lookup x (fst d) of Nothing ->  (vfree_ x); Just v -> v
    iEval_' (Bound_  ii)    d  =  (snd d) !! ii
    iEval_' (i :$: c)       d  =  vapp_ (iEval_ i d) (cEval_ c d)

    iEval_' Nat_                  d  =  VNat_
    iEval_' (NatElim_ m mz ms n)  d
      =  let  mzVal = cEval_ mz d
              msVal = cEval_ ms d
              rec nVal =
                case nVal of
                  VZero_       ->  mzVal
                  VSucc_ k     ->  msVal `vapp_` k `vapp_` rec k
                  VNeutral_ n  ->  VNeutral_
                                   (NNatElim_ (cEval_ m d) mzVal msVal n)
                  _            ->  error "internal: eval natElim"
         in   rec (cEval_ n d)

    iEval_' (Vec_ a n)                 d  =  VVec_ (cEval_ a d) (cEval_ n d)

    iEval_' (VecElim_ a m mn mc n xs)  d  =
      let  mnVal  =  cEval_ mn d
           mcVal  =  cEval_ mc d
           rec nVal xsVal =
             case xsVal of
               VNil_ _          ->  mnVal
               VCons_ _ k x xs  ->  foldl vapp_ mcVal [k, x, xs, rec k xs]
               VNeutral_ n      ->  VNeutral_
                                    (NVecElim_  (cEval_ a d) (cEval_ m d)
                                                mnVal mcVal nVal n)
               _                ->  error "internal: eval vecElim"
      in   rec (cEval_ n d) (cEval_ xs d)

    iEval_' (Eq_ a x y)                d  =  VEq_ (cEval_ a d) (cEval_ x d) (cEval_ y d)
    iEval_' (EqElim_ a m mr x y eq)    d  =
      let  mrVal  =  cEval_ mr d
           rec eqVal =
             case eqVal of
               VRefl_ _ z -> mrVal `vapp_` z
               VNeutral_ n ->
                 VNeutral_ (NEqElim_  (cEval_ a d) (cEval_ m d) mrVal
                                      (cEval_ x d) (cEval_ y d) n)
               _ -> error "internal: eval eqElim"
      in   rec (cEval_ eq d)

    iEval_' (Fin_ n)                d  =  VFin_ (cEval_ n d)
    iEval_' (FinElim_ m mz ms n f)  d  =
      let  mzVal  =  cEval_ mz d
           msVal  =  cEval_ ms d
           rec fVal =
             case fVal of
               VFZero_ k        ->  mzVal `vapp_` k
               VFSucc_ k g      ->  foldl vapp_ msVal [k, g, rec g]
               VNeutral_ n'     ->  VNeutral_
                                    (NFinElim_  (cEval_ m d) (cEval_ mz d)
                                                (cEval_ ms d) (cEval_ n d) n')
               _                ->  error "internal: eval finElim"
      in   rec (cEval_ f d)

iSubst_ :: Int -> ITerm_ -> ITerm_ -> ITerm_
iSubst_ ii i' (L reg it) = L reg $ iSubst_' ii i' it
  where
    iSubst_' ii i'   (Ann_ c c')     =  Ann_ (cSubst_ ii i' c) (cSubst_ ii i' c')


    iSubst_' ii r  Star_           =  Star_
    iSubst_' ii r  (Pi_ ty ty')    =  Pi_  (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')

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

cSubst_ :: Int -> ITerm_ -> CTerm_ -> CTerm_
cSubst_ ii i' (L reg ct) = L reg $ cSubst_' ii i' ct
  where
    cSubst_' ii i' (Inf_ i)      =  Inf_ (iSubst_ ii i' i)
    cSubst_' ii i' (Lam_ c)      =  Lam_ (cSubst_ (ii + 1) i' c)

    cSubst_' ii r  Zero_         =  Zero_
    cSubst_' ii r  (Succ_ n)     =  Succ_ (cSubst_ ii r n)

    cSubst_' ii r  (Nil_ a)      =  Nil_ (cSubst_ ii r a)
    cSubst_' ii r  (Cons_ a n x xs)
                                =  Cons_ (cSubst_ ii r a) (cSubst_ ii r x)
                                         (cSubst_ ii r x) (cSubst_ ii r xs)

    cSubst_' ii r  (Refl_ a x)   =  Refl_ (cSubst_ ii r a) (cSubst_ ii r x)

    cSubst_' ii r  (FZero_ n)    =  FZero_ (cSubst_ ii r n)
    cSubst_' ii r  (FSucc_ n k)  =  FSucc_ (cSubst_ ii r n) (cSubst_ ii r k)

quote_ :: Int -> Value_ -> CTerm_
quote_ ii v = builtin $ quote_' ii v
  where
    pos = startRegion
    quote_' ii (VLam_ t)
      =     Lam_ (quote_ (ii + 1) (t (vfree_ (Quote ii))))


    quote_' ii VStar_ = Inf_ $ L pos Star_
    quote_' ii (VPi_ v f)
        =  Inf_ (L pos $ Pi_ (quote_ ii v) (quote_ (ii + 1) (f (vfree_ (Quote ii)))))

    quote_' ii (VNeutral_ n)
      =     Inf_ (neutralQuote_ ii n)

    quote_' ii VNat_       =  Inf_ $ L pos Nat_
    quote_' ii VZero_      =  Zero_
    quote_' ii (VSucc_ n)  =  Succ_ (quote_ ii n)

    quote_' ii (VVec_ a n)         =  Inf_ (L pos $ Vec_ (quote_ ii a) (quote_ ii n))
    quote_' ii (VNil_ a)           =  Nil_ (quote_ ii a)
    quote_' ii (VCons_ a n x xs)   =  Cons_  (quote_ ii a) (quote_ ii n)
                                            (quote_ ii x) (quote_ ii xs)

    quote_' ii (VEq_ a x y)  =  Inf_ (L pos $ Eq_ (quote_ ii a) (quote_ ii x) (quote_ ii y))
    quote_' ii (VRefl_ a x)  =  Refl_ (quote_ ii a) (quote_ ii x)

    quote_' ii (VFin_ n)           =  Inf_ (L pos $ Fin_ (quote_ ii n))
    quote_' ii (VFZero_ n)         =  FZero_ (quote_ ii n)
    quote_' ii (VFSucc_ n f)       =  FSucc_  (quote_ ii n) (quote_ ii f)

neutralQuote_ :: Int -> Neutral_ -> ITerm_
neutralQuote_ ii (NFree_ v)
   =  boundfree_ ii v
neutralQuote_ ii (NApp_ n v)
   =  neutralQuote_ ii n `globalApp` quote_ ii v

neutralQuote_ ii (NNatElim_ m z s n)
   =  builtin $ NatElim_ (quote_ ii m) (quote_ ii z) (quote_ ii s) (builtin $ Inf_ (neutralQuote_ ii n))

neutralQuote_ ii (NVecElim_ a m mn mc n xs)
   =  builtin $ VecElim_ (quote_ ii a) (quote_ ii m)
               (quote_ ii mn) (quote_ ii mc)
               (quote_ ii n) (builtin $ Inf_ (neutralQuote_ ii xs))

neutralQuote_ ii (NEqElim_ a m mr x y eq)
   =  builtin $ EqElim_  (quote_ ii a) (quote_ ii m) (quote_ ii mr)
               (quote_ ii x) (quote_ ii y)
               (builtin $ Inf_ (neutralQuote_ ii eq))

neutralQuote_ ii (NFinElim_ m mz ms n f)
   =  builtin $ FinElim_ (quote_ ii m)
               (quote_ ii mz) (quote_ ii ms)
               (quote_ ii n) (builtin $ Inf_ (neutralQuote_ ii f))

boundfree_ :: Int -> Name -> ITerm_
boundfree_ ii (Quote k)     =  builtin $ Bound_ ((ii - k - 1) `max` 0)
boundfree_ ii x             =  builtin $ Free_ x

instance Show (Value_ -> Value_) where
  show f = "<<" ++ (show $ quote0_ $ VLam_ f) ++ ">>"

--instance Show Value_ where
--  show = show . quote0_

type Type_     =  Value_


quote0_ :: Value_ -> CTerm_
quote0_ = quote_ 0


data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero n      = n
plus (Succ k) n  = Succ (plus k n)
