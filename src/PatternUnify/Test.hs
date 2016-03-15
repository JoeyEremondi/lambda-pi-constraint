--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE GADTs, KindSignatures, TemplateHaskell, BangPatterns,
      FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
      UndecidableInstances, GeneralizedNewtypeDeriving,
      TypeSynonymInstances, ScopedTypeVariables, PatternSynonyms #-}

-- This module defines test cases for the unification algorithm, divided
-- into those which must succeed, those which should block (possibly
-- succeeding partially), and those which must fail.

module PatternUnify.Test where

import Unbound.Generics.LocallyNameless

import GHC.Generics

import PatternUnify.Kit
import PatternUnify.Tm
import PatternUnify.Unify
import PatternUnify.Context
import PatternUnify.Check

import qualified Data.Either as Either
import qualified Data.Maybe as Maybe

import Debug.Trace (trace)

import Data.List (intercalate)

import qualified Unbound.Generics.LocallyNameless as LN



-- The |test| function executes the constraint solving algorithm on the
-- given metacontext.

test :: [Entry] -> IO ()
test = runTest (const True)


-- Allocate a fresh name so the counter starts from 1, to avoid clashing
-- with s2n (which generates names with index 0):

initialise :: Contextual ()
initialise = (fresh (s2n "init") :: Contextual (Name VAL)) >> return ()

--prettyString t = render $ runPretty $ pretty t

solveEntries :: [Entry] -> Either [(ProbId, Err)] ((), Context)
solveEntries !es  =
  let --intercalate "\n" $ map show es
    !initialContextString = render (runPretty (prettyEntries es)) -- ++ "\nRAW:\n" ++ show es
    result = --trace ("Initial context:\n" ++ initialContextString ) $
       runContextual (B0, map Right es) $ do
          initialise
          ambulando [] []
          validate (const True)
    errString err = ">>>>>>>>>>>>>>\nERROR " ++ err ++ "\nInitial context:\n" ++ initialContextString ++ "\n<<<<<<<<<<<<<<<<<<<<\n"
    resultString = case result of
      Left s -> ">>>>>>>>>>>>>>\nERROR " ++ s ++ "\nInitial context:\n" ++ initialContextString ++ "\n<<<<<<<<<<<<<<<<<<<<\n"
      Right (_, ctx) -> render $ runPretty $ pretty ctx
  in --trace ("\n\n=============\nFinal\n" ++ resultString) $
    case result of
      Left err -> Left [(ProbId $ LN.string2Name "builtinLoc", errString err)]
      Right ((), ctx) -> getContextErrors es ctx


getContextErrors :: [Entry] -> Context -> Either [(ProbId, Err)] ((), Context)
getContextErrors startEntries cx@(lcx, rcx) = do
  let leftErrors = getErrorPairs (trail lcx)
      rightErrors = getErrorPairs (Either.rights rcx)
  case (leftErrors ++ rightErrors) of
    [] -> return ((), cx)
    ret -> Left ret
    where
      getIdent (Prob ident _ _) = Just ident
      getIdent _ = Nothing

      initialIdents = Maybe.catMaybes $ map getIdent startEntries

      isInitial (Prob ident _ _) = ident `Prelude.elem` initialIdents
      isInitial _ = False

      isFailed (Prob _ _ (Failed e)) = True
      isFailed _ = False

      isPending (Prob _ _ (Pending _)) = True
      isPending _ = False

      getErrorPairs :: [Entry] -> [(ProbId, String)]
      getErrorPairs entries =
        let
          failures = filter isFailed entries
          initPending = filter isInitial $ filter isPending entries
          failedInits = map (\(Prob ident _ (Failed s)) -> (ident, s)) $ filter isInitial failures
          pendOnFailed =
            [(ident, err)
            | (Prob failId _ (Failed err)) <- failures
            , (Prob ident _ (Pending pendingOn)) <- initPending
            , failId `Prelude.elem` pendingOn
            ]
        in
          failedInits ++ pendOnFailed



runTest :: (ProblemState -> Bool) -> [Entry] -> IO ()
runTest q es = do
                   putStrLn $ "Raw context:\n" ++ show (map show es)
                   putStrLn $ "Initial context:\n" ++
                                render (runPretty (prettyEntries es))

                   let r = runContextual (B0, map Right es)
                                       (initialise >> ambulando [] [] >> validate q)
                   case r of
                       Left err  -> putStrLn $ "Error: " ++ err
                       Right ((), cx)  -> putStrLn $ "Final context:\n" ++ pp cx ++ "\n"



isFailed :: ProblemState -> Bool
isFailed (Failed _)  = True
isFailed _           = False

lifted :: Nom -> Type -> [Entry] -> [Entry]
lifted x _T es = lift [] es
   where
     lift :: Subs -> [Entry] -> [Entry]
     lift g (E a _A d : as) = E a (_Pi x _T (substs g _A)) d :
                                  lift ((a, runFreshM $ meta a $$ var x) : g) as
     lift g (Prob a p s : as) = Prob a (allProb x _T (substs g p)) s : lift g as
     lift _ [] = []

boy :: String -> Type -> [Entry] -> [Entry]
boy = lifted . s2n

gal :: String -> Type -> Entry
gal x _T = E (s2n x) _T HOLE

eq :: String -> Type -> VAL -> Type -> VAL -> Entry
eq x _S s _T t = Prob (ProbId (s2n x)) (Unify (EQN _S s _T t)) Active
