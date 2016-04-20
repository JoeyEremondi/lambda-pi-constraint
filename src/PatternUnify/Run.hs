--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

-- This module defines test cases for the unification algorithm, divided
-- into those which must succeed, those which should block (possibly
-- succeeding partially), and those which must fail.

module PatternUnify.Run where

import Unbound.Generics.LocallyNameless

import PatternUnify.Check
import PatternUnify.Context
import PatternUnify.Kit
import PatternUnify.Tm
import PatternUnify.Unify

import qualified Data.Either as Either
import qualified Data.Maybe as Maybe

import qualified Data.Map as Map

import Debug.Trace (trace)

--import qualified Unbound.Generics.LocallyNameless as LN

import qualified Data.Graph as Graph

import qualified Top.Implementation.TypeGraph.Class as TC
import qualified Top.Implementation.TypeGraph.ClassMonadic as CM
import qualified Top.Implementation.TypeGraph.Standard as TG

import qualified Top.Util.Empty as Empty

import Top.Implementation.TypeGraph.ApplyHeuristics
import Top.Implementation.TypeGraph.DefaultHeuristics

import System.IO.Unsafe (unsafePerformIO)

-- The |test| function executes the constraint solving algorithm on the
-- given metacontext.

test :: [Entry] -> IO ()
test = runTest (const True)


-- Allocate a fresh name so the counter starts from 1, to avoid clashing
-- with s2n (which generates names with index 0):

initialise :: Contextual ()
initialise = (fresh (s2n "init") :: Contextual (Name VAL)) >> return ()

data ErrorResult =
  ErrorResult
  { errorContext :: Context
  , solverErrs   :: [SolverErr]
  }

data SolverErr = StringErr (ProbId, String) | GraphErr [ErrorInfo ConstraintInfo]

solveEntries :: [Entry] -> Either ErrorResult ((), Context)
solveEntries !es  =
  let --intercalate "\n" $ map show es
    !initialContextString = render (runPretty (prettyEntries es)) -- ++ "\nRAW:\n" ++ show es
    (result, ctx) = trace ("Initial context:\n" ++ initialContextString ) $
       (runContextual (B0, map Right es, error "initial problem ID", Empty.empty, []) $ do
          initialise
          ambulando [] Map.empty
          validResult <- validate (const True)
          badEdges <- applyHeuristics defaultHeuristics
          setMsg  badEdges
          return badEdges
          )  --Make sure we don't crash
    (lcx,rcx,lastProb,_,finalBadEdges) = unsafePerformIO $ do
        let g = (\(_,_,_,g,_) -> g) ctx
        writeFile "out.dot" (TC.toDot g)
        return ctx
    allEntries = lcx ++ (Either.rights rcx)
    depGraph = problemDependenceGraph allEntries es
    leadingToList = initialsDependingOn depGraph (Maybe.catMaybes $ map getIdent es) [lastProb]
    initLoc = case leadingToList of
      [] -> lastProb
      (i:_) -> i
    --errString err = "ERROR " ++ err -- ++ "\nInitial context:\n" ++ initialContextString ++ "\n<<<<<<<<<<<<<<<<<<<<\n"
    -- resultString = case result of
    --   Left s -> ">>>>>>>>>>>>>>\nERROR " ++ s ++ "\nInitial context:\n" ++
    --     initialContextString ++ "\n<<<<<<<<<<<<<<<<<<<<\n"
    --     ++ "\nErrorGraph " ++ finalStr
    --   Right _ -> render $ runPretty $ pretty ctx
  in --trace ("\n\n=============\nFinal\n" ++ resultString) $
    case (finalBadEdges, result) of
      ([], Left err) -> Left $ ErrorResult ctx [StringErr (initLoc, err)]
      ([], Right _) ->
        case getContextErrors es ctx of
          Left errList -> Left $ ErrorResult ctx $ map (\(loc, err) -> StringErr (loc, err)) errList
          Right x -> Right x
      (edgeList, _) ->
        Left $ ErrorResult ctx [GraphErr edgeList]




isFailed (Prob _ _ (Failed e)) = True
isFailed _ = False

isPending (Prob _ _ (Pending _)) = True
isPending _ = False

getIdent (Prob ident _ _) = Just ident
getIdent _ = Nothing

problemDependenceGraph :: [Entry] -> [Entry] -> (Graph.Graph, Graph.Vertex -> (Entry, Nom, [Nom]), Nom -> Maybe Graph.Vertex)
problemDependenceGraph entries startEntries  =
  let

    failures = filter isFailed entries
    allPendings = filter isPending entries



    initialIdents = Maybe.catMaybes $ map getIdent startEntries

    isInitial (Prob ident _ _) = ident `Prelude.elem` initialIdents
    isInitial _ = False

    failEdges pFrom@(Prob idPendingOn _ (Pending pendingOn)) =
      (pFrom, probIdToName idPendingOn,
      [ probIdToName idFailed
      | (Prob idFailed _ (Failed err)) <- failures
      , idFailed `Prelude.elem` pendingOn
      ]
      ++
      [ probIdToName idFailed
      | (Prob idFailed _ _) <- allPendings
      , idFailed `Prelude.elem` pendingOn
      ])
    failEdges _ = undefined
  in
    Graph.graphFromEdges $
        [ failEdges p | p <- allPendings]
        ++ [(failProb, probIdToName idFailed, []) | failProb@(Prob idFailed _ _) <- failures]

initialsDependingOn :: (Graph.Graph, t, Nom -> Maybe Graph.Vertex) -> [ProbId] -> [ProbId] -> [ProbId]
initialsDependingOn (pendGraph, vertToInfo, infoToVert) initialIdents targetIdents =
  let
  in
    [ (initId)
    | initId <- initialIdents
    , failId <- targetIdents
    , (Just vinit) <- [infoToVert $ probIdToName initId]
    , (Just vfail) <- [infoToVert $ probIdToName failId]
    , Graph.path pendGraph vinit vfail
    ]


getContextErrors :: [Entry] -> Context -> Either [(ProbId, Err)] ((), Context)
getContextErrors startEntries cx@(lcx, rcx, _, _,_) = do
  let leftErrors = getErrorPairs (trail lcx)
      rightErrors = getErrorPairs (Either.rights rcx)
  case (leftErrors ++ rightErrors) of
    [] -> return ((), cx)
    ret -> Left ret
    where

      getErrorPairs :: [Entry] -> [(ProbId, String)]
      getErrorPairs entries =
        let
          initialIdents = Maybe.catMaybes $ map getIdent startEntries
          failures = filter isFailed entries
          allPendings = filter isPending entries

          (pendGraph, vertToInfo, infoToVert) = problemDependenceGraph entries startEntries

          failPaths =
            [ (initId, err)
            | initId <- initialIdents
            , (Prob failId _ (Failed err)) <- failures
            , (Just vinit) <- [infoToVert $ probIdToName initId]
            , (Just vfail) <- [infoToVert $ probIdToName failId]
            , Graph.path pendGraph vinit vfail
            ]

        in
          failPaths



runTest :: (ProblemState -> Bool) -> [Entry] -> IO ()
runTest q es = do
                   putStrLn $ "Raw context:\n" ++ show (map show es)
                   putStrLn $ "Initial context:\n" ++
                                render (runPretty (prettyEntries es))

                   let (r,cx) = runContextual (B0, map Right es, error "initial problem ID", Empty.empty, []) $
                                       (do
                                         initialise
                                         ambulando [] Map.empty
                                         validate q)
                   case r of
                       Left err  -> putStrLn $ "Error: " ++ err
                       Right _  -> putStrLn $ "Final context:\n" ++ pp cx ++ "\n"
