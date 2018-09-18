{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
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
import Top.Implementation.TypeGraph.ApplyHeuristics (expandPath, allErrorPaths)
import Top.Implementation.TypeGraph.Basics
import Top.Implementation.TypeGraph.Heuristic
import Top.Implementation.TypeGraph.Path
import qualified Top.Implementation.TypeGraph.Class as Class
import Top.Solver

import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Top.Implementation.TypeGraph.ClassMonadic

import PatternUnify.ConstraintInfo as Info
import PatternUnify.Tm as Tm
import PatternUnify.Check as Check

import Control.Monad

import qualified Unbound.Generics.LocallyNameless as Ln

import Unbound.Generics.LocallyNameless.Unsafe  (unsafeUnbind)

import qualified Control.Monad as Monad

--import Debug.Trace (trace)

import Top.Types.Unification (firstOrderUnify)


import Debug.Trace (trace)

type Info = Info.ConstraintInfo





-----------------------------------------------------------------------------

defaultHeuristics :: Path (EdgeId, Info) -> [Heuristic Info]
defaultHeuristics path =
   [ --avoidDerivedEdges
   listOfVotes
   , highParticipation 1.0 path
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
--Altered from the original to consider edges by their root creator edge
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
    , ctorPermutation
    , appHeuristic
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



instance HasTwoTypes ConstraintInfo where
   getTwoTypes = Info.edgeEqn

ctorPermutation :: (HasTypeGraph m Info) => Selector m Info
ctorPermutation = Selector ("Constructor isomorphism", f)
  where
    f pair@(edge@(EdgeId vc _ _), info) = do
      let rawT = typeOfValues info
      mT <- substituteTypeSafe rawT
      (mt1, mt2) <- getSubstitutedTypes info
      rawVars <- useTypeGraph Class.getVarTypes
      let
        fixVar :: (HasTypeGraph m Info) => Tm.Param -> m (Maybe Tm.Param)
        fixVar = Tm.modifyParam (substituteTypeSafe)
      mVarList <- forM rawVars $ \(n,p) -> fmap (fmap (n,)) $ fixVar p
      let mVars = forM mVarList id
      --fixedVars <- forM vars $ \(n,p) -> (\x -> (n,x)) <$> (Tm.modifyParam (substituteTypeSafe []) p)
      case (mt1, mt2, mT, mVars) of
        (Just t1@(Tm.C can args), Just t2@(Tm.C can2 args2), Just _T, Just vars) | can == can2 -> do
          maybeMatches <- forM (List.permutations args2) $ \permut -> do
             if Check.unsafeEqual vars _T (Tm.C can args) (Tm.C can permut) then
                 return $ Just permut
               else
                 return Nothing
          case (filter (/= args2) $ Maybe.catMaybes maybeMatches) of
            [] ->
              return Nothing
            (match : _) -> do
              let hint = "Rearrange arguments to match " ++ Tm.prettyString t1 ++ " to " ++ Tm.prettyString t2
              return $ Just (8, "Mismatched arguments", [edge], info {maybeHint = Just $ Maybe.fromMaybe hint (maybeHint info)})

        _ -> return Nothing

--Useful helper method



appHeuristic :: (HasTypeGraph m Info) => Selector m Info
appHeuristic = Selector ("Function Application", f)
  where
    maxArgs :: Tm.Type -> Maybe Int
    maxArgs _T = maxArgsHelper _T 0
      where
        maxArgsHelper (Tm.PI _S (Tm.L body)) accum =
          maxArgsHelper (snd $ unsafeUnbind body) (1+accum)
        maxArgsHelper (Tm.N (Tm.Meta _) _) _ = Nothing
        maxArgsHelper _T accum =  Just accum

    --Try to add arguments to fix any mismatches in our function
    -- matchArgs :: (HasTypeGraph m info) => Tm.Type -> [(Tm.VAL, Tm.Type)] -> Tm.Type -> m (Maybe [(VAL, Maybe Type)])
    matchArgs fnTy argTys retTy = 
      -- trace ("MATCH ARGS fn " ++ Tm.prettyString fnTy ++ "  argsTy  " ++ show (map (fmap Tm.prettyString) argTys) ++ "   retTy  " ++ Tm.prettyString retTy) $
      Ln.runFreshMT $ helper fnTy argTys retTy 1 []
      where
        helper :: 
          (HasTypeGraph m Info)
          => VAL
          -> [(VAL, VAL)]
          -> VAL
          -> Integer
          -> [(VAL, Maybe VAL)]
          -> Ln.FreshMT m (Maybe [(VAL, Maybe VAL)])
        helper fnTy [] retTy i accum = do
          _ <- theUnifyTerms (error "TODO INFO") fnTy retTy
          errPaths <- simplifyPath <$> allErrorPaths
          -- let mRet = firstOrderUnify fnTy retTy
          case (errPaths, fnTy) of
            (Fail, _) -> trace ("MATCH RET " ++ Tm.prettyString fnTy ++ "   " ++ Tm.prettyString retTy ++ " ACCUM " ++ show (reverse accum) ) $ 
              return $ Just $ reverse accum
            (_, Tm.PI _S _T) -> do
              argVal <- Tm.var <$> Tm.freshNom
              _TVal <- _T Tm.$$ argVal
              helper _TVal [] retTy (i+1) $ (argVal, Just _S) : accum
            _ -> return Nothing
        helper (Tm.PI _S _T) argsList@((argVal, argTy) : argsRest) retTy i accum = do
          -- let mUnifArgTy = firstOrderUnify _S argTy 
          _ <- theUnifyTerms (error "TODO INFO 2") _S argTy
          errPaths <- simplifyPath <$> allErrorPaths
          case errPaths of
            Fail -> do
              _TVal <- _T Tm.$$ argVal
              trace ("MATCH type " ++ Tm.prettyString _S ++ " to " ++ Tm.prettyString argTy ++ " TVal : " ++ Tm.prettyString _TVal) $
                helper _TVal argsRest retTy (i+1) $ (argVal, Nothing) : accum
            _ -> do
              argVal <- Tm.var <$> Tm.freshNom
              _TVal <- _T Tm.$$ argVal
              helper _TVal argsList retTy (i+1) $ (argVal, Just _S) : accum
        helper fnTy argTys retTy i accum = return Nothing

    f pair@(edge@(EdgeId vc _ _), info) | Just reg <- (applicationEdgeRegion $ programContext $ edgeEqnInfo info) = do
      --let (fnTyEdge:_) = [x | x <- edges]

      edges <- allEdges
      --TODO don't clear out right edges from choice? Preserve CF edges?
      let appEdges = [edge | edge <- edges, Just subReg <- [applicationEdgeRegion $ programContext $ edgeEqnInfo (snd edge)], subReg == reg, not (isRightEdge $ edgeType $ snd edge)]
      let (Application reg argNum fnStr rawFnTy rawArgs rawRetType frees) : _ =
            [pcon | edge <- appEdges , pcon <- [programContext $ edgeEqnInfo $ snd edge] , (Application _ _ _ _ _ _ _) <- [pcon]]
      --let argAppEdges  = [edge | edge <- appEdges , pcon <- [programContext $ edgeEqnInfo $ snd edge] , (Application _ _ _ _ _) <- [pcon]]
      --let (fnTy, fnStr, fnAppEdge) : _ = _[(fTy, fnStr, pr) | pr <- appEdges, AppFnType subReg fnStr fTy <- [programContext $ edgeEqnInfo $ snd pr], subReg == reg]
      --let (fnRetEdge ) : _ = [(pr) | pr <- appEdges, AppRetType subReg _ <- [programContext $ edgeEqnInfo $ snd pr], subReg == reg]

      let edgeContext = programContext $ edgeEqnInfo info



      (mFullFnTp, maybeArgList, mRetTy) <- doWithoutEdges appEdges $ do
        -- limitedDot <- getDot
        fullFn <- substituteTypeSafe $ rawFnTy
        argMaybeList <- forM rawArgs $ \(aval, aty) -> do
          retVal <- substituteTypeSafe $ aval
          retTy <-  substituteTypeSafe $ aty
          return $ case (retVal, retTy) of
            (Just x, Just y) ->
              Just (x,y)
            _ -> Nothing
        mRetTy <- substituteTypeSafe   rawRetType

        return (fullFn, Monad.sequence argMaybeList, mRetTy)

      let
        argTypeHints (v, Just t) = Just $  Tm.prettyString v ++ " :: " ++ Tm.prettyString t
        argTypeHints _ = Nothing


        argPermuts args = args : (permutations args)
        makeMatch  localFnType retTy permut  = freezeTypeGraphM $  matchArgs localFnType permut retTy
        ourMatch localFnType retTy args = do 
          mMatches <- forM (argPermuts args) (makeMatch localFnType  retTy) 
          case filter (\l -> map fst l /= (map fst args) ) $ Maybe.catMaybes mMatches of
            [] -> return Nothing
            l@(h:_) -> trace ("Got argPermuts " ++ show l ++ "  from  " ++ show args) $ return $ Just h

      let numArgsProvided = length rawArgs

      case mFullFnTp of
        Just fullFnTp -> do
          let
            fnMax = case maxArgs fullFnTp of
              Just n -> n
              Nothing -> numArgsProvided
          case () of
            ()
              | fnMax < numArgsProvided -> do
                let hint = "Function expected at most " ++ show fnMax ++ " arguments, but you gave " ++ show (numArgsProvided)
                return $ Just (10, "Too many arguments", [edge], info {maybeHint = Just hint})

              | Just retTy <- mRetTy
              , Just actualArgs <- maybeArgList
              --,  n >= length args
              -- , (AppFnType _ _ _ ) <- edgeContext
               -> do
                mMatchList <- ourMatch fullFnTp retTy actualArgs
                case mMatchList of
                  Just matchList -> do
                    let argStr t = "(" ++ Tm.prettyString t ++ ")"
                    let expectedArgsStr
                          | length matchList > numArgsProvided =
                            "Function expected " ++ show fnMax ++ " arguments, but you gave "
                               ++ show (numArgsProvided)
                          | length matchList == numArgsProvided =
                            "Function arguments in the wrong order"
                    let
                      argHintsList = (Maybe.catMaybes $ map argTypeHints matchList)
                      whereStr [] = ""
                      whereStr l = "\n      where\n        "
                        ++ List.intercalate "\n        " l

                    let hint = expectedArgsStr ++ ". Try (" ++ show fnStr ++ ") "
                          ++ List.intercalate " " (map (argStr . fst) matchList)
                          ++ whereStr argHintsList
                    return $ Just (100, "Too few or mismatched arguments", [edge], info {maybeHint = Just hint})
                  _ -> return Nothing
            _ -> return Nothing
        _ -> return Nothing

    f _ = return Nothing

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
