module Main where

import qualified ConstraintBased as CB
import Common

import System.Environment (getArgs)

import PatternUnify.Tm as Tm

import Constraint as Constraint

import PatternUnify.Kit

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] ->
      repLP CB.checker True
    (fileName:_) -> do
      compileFile (lp CB.checker) (True, [], lpve, lpte) fileName
      return ()


lp :: TypeChecker -> Interpreter ITerm_ CTerm_ Tm.VAL Tm.VAL CTerm_ Tm.VAL
lp checker = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \ v c -> checker (v, c),
         iquote = error "TODO quote",
         ieval = \e x -> Constraint.constrEval (lpte, e) x,
         ihastype = id,
         icprint = cPrint_ 0 0,
         itprint = runPretty . pretty,
         iiparse = parseITerm_ 0 [],
         isparse = parseStmt_ [],
         iassume = \ s (x, t) -> lpassume checker s x t }


repLP :: TypeChecker -> Bool -> IO ()
repLP checker b = readevalprint (lp checker) (b, [], lpve, lpte)

lpassume checker state@(inter, out, ve, te) x t =
  check (lp checker) state x (builtin $ Ann_ t (builtin $ Inf_ $ builtin $ Star_))
        (\ (y, v) -> return ())
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))
