{-# LANGUAGE FlexibleInstances, PatternSynonyms #-}
module Parse where

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



parseType :: Int -> [String] -> LPParser Type
parseType 0 e =
  try
     (do
        t <- parseType 1 e
        rest t <|> return t)
  where
    rest t =
      do
        reserved simplyTyped "->"
        t' <- parseType 0 e
        return (Fun t t')
parseType 1 e =
      do
        x <- identifier simplyTyped
        return (TFree (Global x))
  <|> parens simplyTyped (parseType 0 e)


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

tPrint :: Int -> Type -> Doc
tPrint p (TFree (Global s))  =  text s
tPrint p (Fun ty ty')        =  parensIf (p > 0) (sep [tPrint 0 ty <> text " ->", nest 2 (tPrint 0 ty')])

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
