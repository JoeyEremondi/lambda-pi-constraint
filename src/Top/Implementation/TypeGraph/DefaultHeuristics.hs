{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS -Wall #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  portable
-----------------------------------------------------------------------------

module Top.Implementation.TypeGraph.DefaultHeuristics where

import Data.List
import qualified Data.Map as M
import Top.Implementation.TypeGraph.ApplyHeuristics (expandPath)
import Top.Implementation.TypeGraph.Basics
import Top.Implementation.TypeGraph.Heuristic
import Top.Implementation.TypeGraph.Path
import Top.Solver

import Top.Implementation.TypeGraph.ClassMonadic

import PatternUnify.ConstraintInfo as Info
import PatternUnify.Tm as Tm

type Info = Info.ConstraintInfo

--import Debug.Trace (trace)

-----------------------------------------------------------------------------

defaultHeuristics :: Path (EdgeId, Info) -> [Heuristic Info]
defaultHeuristics path =
   [ avoidDerivedEdges
   , listOfVotes
   , highParticipation 0.80 path
   , firstComeFirstBlamed ]

-----------------------------------------------------------------------------

-- |Compute the smallest 'minimal' sets. This computation is very(!) costly
--   (might take a long time for complex inconsistencies)
inMininalSet :: Path (EdgeId, info) -> Heuristic info
inMininalSet path =
   Heuristic (
      let sets       = minimalSets eqInfo2 path
          candidates = nubBy eqInfo2 (concat sets)
          f e        = return (any (eqInfo2 e) candidates)
      in edgeFilter "In a smallest minimal set" f)

-- |Although not as precise as the minimal set analysis, this calculates the participation of
-- each edge in all error paths.
-- Default ratio = 1.0  (100 percent)
--   (the ratio determines which scores compared to the best are accepted)
highParticipation :: Show info => Double -> Path (EdgeId, info) -> Heuristic info
highParticipation ratio path =
   Heuristic (Filter ("Participation ratio [ratio="++show ratio++"]") selectTheBest)
 where
   selectTheBest es =
      let (nrOfPaths, fm)   = participationMap (mapPath (\(EdgeId _ _ cnr,_) -> cnr) path)
          participationList = M.filterWithKey p fm
          p cnr _    = cnr `elem` activeCNrs
          activeCNrs = [ cnr | (EdgeId _ _ cnr, _) <- es ]
          maxInList  = maximum (M.elems participationList)
          limit     -- test if one edge can solve it completely
             | maxInList == nrOfPaths = maxInList
             | otherwise              = round (fromIntegral maxInList * ratio) `max` 1
          goodCNrs   = M.keys (M.filter (>= limit) participationList)
          bestEdges  = filter (\(EdgeId _ _ cnr,_) -> cnr `elem` goodCNrs) es

          -- prints a nice report
          mymsg  = unlines ("" : title : replicate 50 '-' : map f es)
          title  = "cnr  edge          ratio   info"
          f (edgeID@(EdgeId _ _ cnr),info) =
             take 5  (show cnr++(if cnr `elem` goodCNrs then "*" else "")++repeat ' ') ++
             take 14 (show edgeID++repeat ' ') ++
             take 8  (show (M.findWithDefault 0 cnr fm * 100 `div` nrOfPaths)++"%"++repeat ' ') ++
             "{"++show info++"}"
      in do logMsg mymsg
            return bestEdges

-- |Select the "latest" constraint
firstComeFirstBlamed :: Heuristic info
firstComeFirstBlamed =
   Heuristic (
      let f (EdgeId _ _ cnr, _) = return cnr
      in maximalEdgeFilter "First come, first blamed" f)

-- |Select only specific constraint numbers
selectConstraintNumbers :: [EdgeNr] -> Heuristic info
selectConstraintNumbers is =
   Heuristic (
      let f (EdgeId _ _ cnr, _) = return (cnr `elem` is)
      in edgeFilter ("select constraint numbers " ++ show is) f)


-- |Select only specific constraint numbers
avoidDerivedEdges :: Heuristic Info
avoidDerivedEdges =
   Heuristic (
      let f (_, info) = return $ (Info.creationInfo . Info.edgeEqnInfo) info == Info.Initial
      in edgeFilter ("avoid derived edges ") f)


listOfVotes =
  Heuristic $ Voting $
    [ preferChoiceEdges
    ]

preferChoiceEdges :: (HasTypeGraph m Info) => Selector m Info
preferChoiceEdges = Selector ("Choice edges", f)
  where
    f pair@(edge@(EdgeId vc _ _), info) = case Info.edgeType info of
      ChoiceEdge Info.LeftChoice _ _ -> do
        currentConstants <- constantsInGroupOf vc
        newConstants <- doWithoutEdge pair $ constantsInGroupOf vc
        case (length currentConstants > length newConstants) of
          True -> return $ Just (10, "Choice", [edge], info)
          _ -> return Nothing
      _ -> return Nothing


ctorPermutation :: (HasTypeGraph m Info) => Selector m Info
ctorPermutation = Selector ("Constructor isomorphism", f)
  where
    f pair@(edge@(EdgeId vc _ _), info) = do
      (t1, t2) <- getSubstitutedTypes info
      case (t1, t2) of
        (Just (Tm.C can args), Just (Tm.C can2 args2)) | can == can2 ->
          return _
        _ -> return _
      return _

-- -- |Select only the constraints for which there is evidence in the predicates
-- -- of the current state that the constraint at hand is incorrect.
-- inPredicatePath :: Heuristic info
-- inPredicatePath =
--    Heuristic (Filter "in a predicate path" f) where
--
--     f xs =
--        do pp  <- predicatePath
--           path <- expandPath (simplifyPath pp)
--           let cnrs = nub [ c | (EdgeId _ _ c, _) <- steps path ]
--               p (EdgeId _ _ cnr, _) = cnr `elem` cnrs
--               ys = filter p xs
--           return (if null ys then xs else ys)
