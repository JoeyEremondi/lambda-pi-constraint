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

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import PatternUnify.SolverConfig

--import Debug.Trace (trace)

--import qualified Unbound.Generics.LocallyNameless as LN

import qualified Data.Graph as Graph

import qualified Top.Implementation.TypeGraph.Class as TC
import qualified Top.Implementation.TypeGraph.ClassMonadic as CM
import qualified Top.Implementation.TypeGraph.Standard as TG

import qualified Top.Util.Empty as Empty

import Top.Implementation.TypeGraph.ApplyHeuristics
import Top.Implementation.TypeGraph.DefaultHeuristics

import System.IO.Unsafe (unsafePerformIO)

import PatternUnify.Tm (Region (..))

import Control.Monad(when)

import Debug.Trace (trace)


-- Allocate a fresh name so the counter starts from 1, to avoid clashing
-- with s2n (which generates names with index 0):

initialise :: Contextual ()
initialise = (fresh (s2n "init") :: Contextual (Name VAL)) >> return ()

data ErrorResult =
  ErrorResult
  { errorContext :: Context
  , solverErrs   :: [SolverErr]
  }

data SolverErr = StringErr (ProbId, Region, String) | GraphErr [ErrorInfo ConstraintInfo]

solveEntries :: SolverConfig -> [Entry] -> Either ErrorResult ((), Context)
solveEntries conf !es  =
  let --intercalate "\n" $ map show es
    !initialContextString = render (runPretty (prettyEntries es)) -- ++ "\nRAW:\n" ++ show es
    entryPid (Prob p _ _ _ ) = Just p
    entryPid _ = Nothing
    infoString e = (typeOfString $ entryInfo e, entryPid e)  
    (result, ctx) = trace ("Initial context:\n" ++ initialContextString ++ "\n" ++ List.intercalate "\n" (map (show . infoString) es) ) $
       (runContextual ( Context B0  (map Right es) (error "initial problem ID") Empty.empty [] Set.empty conf Map.empty) $ do
          initialise
          ambulando [] [] Map.empty
          --validResult <- validate (const True)
          badEdges <- applyHeuristics defaultHeuristics
          case badEdges of
            [] -> validate (\_ -> True) -- $shouldValidate
            _ -> return () 
          setMsg  badEdges
          return badEdges
          )  --Make sure we don't crash
    Context lcx rcx lastProb _ finalBadEdges _ _ _ = unsafePerformIO $ do
        let g = contextGraph ctx
        let ourEdges = contextBadEdges ctx
        when (useDot conf) $ writeFile "out.dot" (
          TC.toDot g
          -- List.intercalate "\n\n\n" $
          --   map (\(edgeList, _) -> TC.errorDot edgeList g) ourEdges
            )
        return ctx
    allEntries = lcx ++ (Either.rights rcx)
    depGraph = problemDependenceGraph allEntries es
    leadingToList = initialsDependingOn depGraph (Maybe.catMaybes $ map getIdent es) [lastProb]
    initLoc = case leadingToList of
      [] -> lastProb
      (i:_) -> i
    -- errString err = "ERROR " ++ err -- ++ "\nInitial context:\n" ++ initialContextString ++ "\n<<<<<<<<<<<<<<<<<<<<\n"
    -- resultString = case result of
    --   Left s -> ">>>>>>>>>>>>>>\nERROR " ++ s ++ "\nInitial context:\n" ++
    --     initialContextString ++ "\n<<<<<<<<<<<<<<<<<<<<\n"
    --     ++ "\nErrorGraph " ++ finalStr
    --   Right _ -> render $ runPretty $ pretty ctx
  in --trace ("\n\n=============\nFinal\n" ++ List.intercalate "\n" (map pp lcx)) $
    case (finalBadEdges, result) of
      ([], Left err) -> --trace ("ERR NO EDGES") $
        Left $ ErrorResult ctx [StringErr (initLoc, BuiltinRegion, err)]
      ([], Right _) ->
        case getContextErrors es ctx of
          Left [] -> error "Empty Left from getContextErrors"
          Left errList -> Left $ ErrorResult ctx $ map (\(loc, reg, err) -> StringErr (loc, reg, err)) errList
          Right x -> Right x
      (edgeList, _) -> --trace ("EDGELIST\n  " ++ List.intercalate "\n  " (map show edgeList)) $
        Left $ ErrorResult ctx [GraphErr edgeList]




isFailed (Prob _ _ (Failed e) _) = True
isFailed _ = False

isPending (Prob _ _ (Pending _) _) = True
isPending _ = False

getIdent (Prob ident _ _ _) = Just ident
getIdent _ = Nothing

problemDependenceGraph :: [Entry] -> [Entry] -> (Graph.Graph, Graph.Vertex -> (Entry, Nom, [Nom]), Nom -> Maybe Graph.Vertex)
problemDependenceGraph entries startEntries  =
  let

    failures = filter isFailed entries
    allPendings = filter isPending entries



    initialIdents = Maybe.catMaybes $ map getIdent startEntries

    isInitial (Prob ident _ _ _) = ident `Prelude.elem` initialIdents
    isInitial _ = False

    failEdges pFrom@(Prob idPendingOn _ (Pending pendingOn) _) =
      (pFrom, probIdToName idPendingOn,
      [ probIdToName idFailed
      | (Prob idFailed _ (Failed err) _) <- failures
      , idFailed `Prelude.elem` pendingOn
      ]
      ++
      [ probIdToName idFailed
      | (Prob idFailed _ _ _) <- allPendings
      , idFailed `Prelude.elem` pendingOn
      ])
    failEdges _ = undefined
  in
    Graph.graphFromEdges $
        [ failEdges p | p <- allPendings]
        ++ [(failProb, probIdToName idFailed, []) | failProb@(Prob idFailed _ _ _) <- failures]

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



getContextErrors :: [Entry] -> Context -> Either [(ProbId, Region, Err)] ((), Context)
getContextErrors startEntries cx@(Context lcx rcx _ _ _ _ _ _) = do
  let leftErrors = getErrorPairs (trail lcx)
      rightErrors = getErrorPairs (Either.rights rcx)
  case (leftErrors ++ rightErrors) of
    [] -> return ((), cx)
    ret -> Left ret
    where

      getErrorPairs :: [Entry] -> [(ProbId, Region, String)]
      getErrorPairs entries =
        let
          initialIdents = Maybe.catMaybes $ map getIdent startEntries
          failures = filter isFailed entries
          allPendings = filter isPending entries

          (pendGraph, vertToInfo, infoToVert) = problemDependenceGraph entries startEntries

          failPaths =
            [ (initId, infoRegion $ probInfo failProb, err)
            | initId <- initialIdents
            , (Prob failId failProb (Failed err) _) <- failures
            , (Just vinit) <- [infoToVert $ probIdToName initId]
            , (Just vfail) <- [infoToVert $ probIdToName failId]
            , Graph.path pendGraph vinit vfail
            ]

        in
          failPaths
