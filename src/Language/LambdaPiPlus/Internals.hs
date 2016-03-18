{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.LambdaPiPlus.Internals
  where

import Common
import qualified ConstraintBased as CB
import Main
import qualified PatternUnify.Tm as Tm
import Text.Parsec
import Text.Parsec.Pos (SourcePos)

import qualified Unbound.Generics.LocallyNameless as LN


import Language.Haskell.TH.Lift

import Control.Monad (foldM)

type CompileContext = Common.State Tm.VAL Tm.VAL
type CompileResult = Either [(Maybe SourcePos, String)] CompileContext

emptyContext = (True, [], lpve, lpte)


int = lp CB.checker

compile :: String -> CompileContext -> (CompileResult)
compile source context = do
  stmts <- parseSimple "editor-window" (many (isparse int)) source
  foldM (doStmt $ lp CB.checker) context stmts


doStmt :: LpInterp
              -> CompileContext -> Stmt ITerm_ CTerm_ -> CompileResult
doStmt int state@(inter, out, ve, te) stmt =
  do
    case stmt of
        Assume assm -> foldM (doAssume) state assm
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> error "TODO implement write to console"--putStrLn x >> return state
        Out f      -> return (inter, f, ve, te)
  where
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      doCheck int state i t
        (\ (y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype int y) : te))

doAssume :: CompileContext -> (String, CTerm_) -> CompileResult
doAssume  state@(inter, out, ve, te) (x, t) =
  doCheck (lp CB.checker) state x (builtin $ Ann_ t (builtin $ Inf_ $ builtin $ Star_))
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))

doCheck :: LpInterp -> CompileContext -> String -> ITerm_
          -> ((Tm.Type, Tm.VAL) -> CompileContext) -> CompileResult
doCheck int state@(inter, out, ve, te) i t k =
                do
                  --  typecheck and evaluate
                  (y, newVal, subs) <- iitype int ve te t
                  let v = ieval int ve t
                  return (k (y, newVal))


$(deriveLiftMany [''Common.Name, ''Common.ITerm_', ''Common.CTerm_', ''Common.Located, ''Common.Region, ''SourcePos, ''LN.Name, ''LN.Bind, ''Tm.Elim, ''Tm.Head, ''Tm.Twin, ''Tm.Can, ''Tm.VAL])
