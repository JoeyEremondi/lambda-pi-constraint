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

import qualified PatternUnify.Tm as Tm

data Region =
  SourceRegion SourcePos
  | BuiltinRegion
  deriving (Eq, Ord, Show)

prettySource :: Region -> String
prettySource (SourceRegion pos) =
   (show $ sourceLine pos) ++ ":" ++ (show $ sourceColumn pos)
prettySource s = "builtin:"


data Located a = L {region :: Region, contents :: a}
  deriving (Eq, Ord, Show)

type LPParser = P.ParsecT String SourcePos Identity

startRegion = SourceRegion $ Pos.initialPos ""

catch = catchIOError

builtin x = L BuiltinRegion x

getRegion = SourceRegion `fmap` getPosition


putstrln x = putStrLn x

simplyTyped = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                              reservedNames = ["let", "assume", "putStrLn"] })





vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id


lambdaPi = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                           reservedNames = ["forall", "let", "assume", "putStrLn", "out"] })



parseBindings_ :: Bool -> [String] -> LPParser ([String], [Tm.VAL])
parseBindings_ b e =
                   (let rec :: [String] -> [Tm.VAL] -> LPParser ([String], [Tm.VAL])
                        rec e ts =
                          do
                           (x,t) <- parens lambdaPi
                                      (do
                                         x <- identifier lambdaPi
                                         reserved lambdaPi "::"
                                         t <- parseVal 0 (if b then e else [])
                                         return (x,t))
                           (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                    in rec e [])
                   <|>
                   do  x <- identifier lambdaPi
                       reserved lambdaPi "::"
                       t <- parseVal 0 e
                       return (x : e, [t])

parseVal :: Int -> [String] -> LPParser Tm.VAL
parseVal 0 e =
  getRegion >>= \pos ->
  parseLam_ e
    <|> fmap (\x -> L pos x) (parseVal 0 e)
    <|>
      do
        reserved lambdaPi "forall"
        (fe,t:ts) <- parseBindings_ True e
        reserved lambdaPi "."
        t' <- parseVal 0 fe
        return (foldl (\ p t -> L pos $ Tm.PI t p) (L pos $  Tm.PI t t') ts)
  <|>
  try
     (do
        t <- parseVal 1 e
        rest t <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam_ e)
        rest t
  where
    rest t =
      do
        pos <- getRegion
        reserved lambdaPi "->"
        t' <- parseVal 0 ([]:e)
        return (L pos $ Tm.PI t t')
parseVal 1 e = getRegion >>= \pos ->
  try
     (do
        t <- parseVal 2 e
        rest t <|> return t)
  <|> do
        t <- parens lambdaPi (parseLam_ e)
        rest t
  where
    rest t =
      do
        pos <- getRegion
        reserved lambdaPi "::"
        t' <- parseVal 0 e
        return (L pos $ Tm.AnnVal t t')
parseVal 2 e =
      do
        pos <- getRegion
        t <- parseVal 3 e
        ts <- many (parseVal 3 e)
        let app x y = L pos (x Tm.$$ y)
        return (foldl app t ts)
parseVal 3 e = getRegion >>= \pos ->
      do
        reserved lambdaPi "*"
        return $ L pos Tm.SET
  <|> do
        n <- natural lambdaPi
        return $ error "TODO Nat" --(toNat_ pos n)
  <|> do
        x <- identifier lambdaPi
        return $ Tm.vv x
  <|> parens lambdaPi (parseVal 0 e)

parseVal p e =  getRegion >>= \pos ->
      try (parens lambdaPi (parseLam_ e))
  <|> fmap (L pos) (parseVal p e)

parseLam_ :: [String] -> LPParser Tm.VAL
parseLam_ e =
      do
         pos <- getRegion
         let mkLam x = L pos (Tm.L x)
         reservedOp lambdaPi "\\"
         xs <- many1 (identifier lambdaPi)
         reservedOp lambdaPi "->"
         t <- parseVal 0 (reverse xs ++ e)
         --  reserved lambdaPi "."
         return (iterate mkLam t !! length xs)
