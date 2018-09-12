module Main where

import Common
import qualified ConstraintBased as CB

import System.Environment (getArgs)

import PatternUnify.Tm as Tm

import Constraint as Constraint

import PatternUnify.Kit

import Top.Implementation.TypeGraph.Class

import qualified Data.List as List
import PatternUnify.SolverConfig
import PatternUnify.Tm (Region (..))

main :: IO ()
main = do
  argsWithFlags <- getArgs
  let config = SolverConfig (not $ "--noCF" `Prelude.elem` argsWithFlags) (not $ "--noTypeGraph" `Prelude.elem` argsWithFlags) (not $ "--noDot" `Prelude.elem` argsWithFlags)
  let args = filter (not . (List.isPrefixOf "--")) argsWithFlags
  case args of
    [] ->
      repLP (CB.checker config) True
    (fileName:_) -> do
      compileFile (lp $ CB.checker config) (True, [], lpve, lpte) fileName
      return ()

type LpInterp = Interpreter ITerm_ CTerm_ Tm.VAL Tm.VAL CTerm_ Tm.VAL

lp :: TypeChecker -> Interpreter ITerm_ CTerm_ Tm.VAL Tm.VAL CTerm_ Tm.VAL
lp checker = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \ v c -> checker (v, c),
         iquote = error "TODO quote",
         ieval = \e x -> Constraint.constrEval (lpte, e) x,
         ihastype = id,
         icprint = cPrint_ 0 0,
         itprint = runPretty . pretty,
         ivprint = runPretty . pretty,
         iiparse = parseITerm_ 0 [],
         isparse = parseStmt_ [],
         iassume = \ s (x, t) -> lpassume checker s x t }


repLP :: TypeChecker -> Bool -> IO ()
repLP checker b = readevalprint (lp checker) (b, [], lpve, lpte)

lpassume checker state@(inter, out, ve, te) x t =
  check (lp checker) state x (builtin $ Ann_ t (builtin $ Inf_ $ builtin $ Star_))
        (\ (y, v, _) -> return ())
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))
