{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Language.LambdaPiPlus.Internals
  where

import Common
import qualified ConstraintBased as CB
import Main
import qualified PatternUnify.Tm as Tm
import Text.Parsec
import Text.Parsec.Pos (SourcePos)

import Control.Monad.Writer

import qualified Unbound.Generics.LocallyNameless as LN


import Language.Haskell.TH.Lift

import Control.Monad (foldM)

type CompileM = Either [(Maybe SourcePos, String)]

type CompileContext = Common.State Tm.VAL Tm.VAL
type ParseResult =  [Stmt ITerm_ CTerm_]

emptyContext = (True, [], lpve, lpte)


int = lp CB.checker

parse :: String -> CompileM ParseResult
parse source = parseSimple "editor-window" (many (isparse int)) source

compile :: [Stmt ITerm_ CTerm_] -> CompileContext -> CompileM (CompileContext, String)
compile stmts context =
  foldM (doStmt $ lp CB.checker) (context, "") stmts


doStmt :: LpInterp
              -> (CompileContext, String) -> Stmt ITerm_ CTerm_ -> CompileM (CompileContext, String)
doStmt int (state@(inter, out, ve, te), output) stmt =
  do
    case stmt of
        Assume assm -> foldM (doAssume) (state, output) assm
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> return (state, output ++ x ++"\n")
        Out f      -> return ((inter, f, ve, te), output)
  where
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      doCheck int (state, output) i t
        (\ (y, v) -> ((inter, "", (Global i, v) : ve, (Global i, ihastype int y) : te)))

modOutput ident y v subs output =
  output
  ++ makeOutText int ident y v subs ++ "\n"
  ++ solvedMetasString int subs ++ "\n\n"

doAssume :: (CompileContext, String) -> (String, CTerm_) -> CompileM (CompileContext, String)
doAssume  (state@(inter, out, ve, te), output) (x, t) =
  doCheck (lp CB.checker) (state, output) x (builtin $ Ann_ t (builtin $ Inf_ $ builtin $ Star_))
        (\ (y, v) -> ((inter, out, ve, (Global x, v) : te)))


doCheck :: LpInterp -> (CompileContext, String) -> String -> ITerm_
           -> ((Tm.Type, Tm.VAL) -> CompileContext) -> CompileM (CompileContext, String)
doCheck int (state@(inter, out, ve, te), output) ident t k =
                do
                  --  typecheck and evaluate
                  (y, newVal, subs) <- iitype int ve te t
                  let v = ieval int ve t
                  return (k (y, newVal), modOutput ident y v subs output)


$(deriveLiftMany [''Common.Name, ''Common.ITerm_', ''Common.CTerm_', ''Common.Located, ''Common.Region, ''SourcePos, ''LN.Name, ''LN.Bind, ''Tm.Elim, ''Tm.Head, ''Tm.Twin, ''Tm.Can, ''Tm.VAL])
