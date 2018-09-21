{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------
module Top.Implementation.TypeGraph.ApplyHeuristics (applyHeuristics,  expandPath, ErrorInfo, EndpointInfo, HeuristicInput(..)) where

import Data.Graph (buildG, scc)
import Data.List
import Data.Function
import Data.Tree (flatten)
import qualified Data.Map as M
import qualified Data.Set as S
import Top.Implementation.TypeGraph.Basics
import Top.Implementation.TypeGraph.ClassMonadic
import qualified Top.Implementation.TypeGraph.Class as Class
import Top.Implementation.TypeGraph.Heuristic
import Top.Implementation.TypeGraph.Path
--import Top.Interface.Qualification hiding (contextReduction)
--import Top.Interface.TypeInference
import Top.Solver
import Top.Types
import Utils (internalError)

import qualified PatternUnify.Tm as Tm
import qualified Data.List as List

-- import Debug.Trace (trace)

import Data.Maybe (listToMaybe, catMaybes)

import Debug.Trace (trace)

type ErrorInfo info = ([EdgeId], info)

data HeuristicInput info = HInput
  { hEndpointInfo :: EndpointInfo info
  , hErrorPath :: Path (EdgeId, info)
  , hAllEdges :: [(EdgeId, info)]
  , hCreatorMap :: M.Map EdgeId (EdgeId, info)
  }

type EndpointInfo info = [(Tm.VAL, [info])]

applyHeuristics :: forall m info . HasTypeGraph m info =>(HeuristicInput info -> [Heuristic info]) -> m [ErrorInfo info]
applyHeuristics heuristics =
   let rec hInfo =
          case simplifyPath (hErrorPath hInfo) of
             Empty -> internalError "Top.TypeGraph.ApplyHeuristics" "applyHeuristics" "unexpected empty path"
             Fail  -> return []
             path  ->
                do err <- evalHeuristics path $ heuristics (hInfo {hErrorPath = path})
                   let errList = [(e,snd err) | e <- fst err]
                   mDeletedCreators <- forM errList getEdgeCreator
                   let deletedCreators = map fst $ catMaybes mDeletedCreators 
                   let allSteps = steps path 
                   let creatorMap = hCreatorMap hInfo
                   let deletedEdges :: [EdgeId]
                       deletedEdges = fst err ++ [e | (e,_) <- allSteps, Just (c,_) <- [M.lookup e creatorMap], c `elem` deletedCreators ]
                   let restPath =
                         changeStep (\t@(a,_) -> if a `elem` deletedEdges then Fail else Step t) path
                   errs <- rec (hInfo {hErrorPath = restPath})
                   return (err : errs) 
   in
      do hInfo <- allErrorPaths
         rec $ hInfo {hErrorPath = removeSomeDuplicates info2ToEdgeNr (hErrorPath hInfo)}

-- These functions are used to describe for a change due to a heuristic how it affected the error path
-- showing whether the set of constraints shrunk and if so, whether it has now become a singleton.
tag :: String -> String
tag s = "~" ++ s ++ "~" 

shrunkAndFinalMsg :: [a] -> [a] -> String
shrunkAndFinalMsg old new =
  if length new < length old then
    if length new == 1 then
      tag "shrunk" ++ " " ++ tag "final"
    else
      tag "shrunk"
  else
    tag "unmodified"


evalHeuristics :: HasTypeGraph m info => Path (EdgeId, info) -> [Heuristic info] -> m (ErrorInfo info)
evalHeuristics path = rec edgesBegin
 where
   edgesBegin = nubBy eqInfo2 (steps path)

   rec edges [] =
      case edges of
         (edgeId@(EdgeId _ _ cnr), info) : _ ->
            do logMsg ("\n*** The selected constraint: " ++ show cnr ++ " ***\n")
               return ([edgeId], info)
         _ -> internalError "Top.TypeGraph.ApplyHeuristics" "evalHeuristics" "empty list"

   rec edges (Heuristic heuristic:rest) =
      case heuristic of

         Filter name f ->
            do edges' <- f edges
               --logMsg (name ++ " (filter) " ++ shrunkAndFinalMsg edges edges')
               --logMsg ("   " ++ showSet [ i | (EdgeId _ _ i, _) <- edges' ])
               rec edges' rest

         Voting selectors ->
            do logMsg ("Voting with "++show (length selectors) ++ " heuristics")
               results <- mapM (evalSelector edges) selectors
               let successList = [ (getSelectorName s, x) | (s, xs) <- zip selectors results, x <- xs ]
                   (thePrio, listWithBest) = foldr op (minBound, []) successList
                   op (selname, (prio, es, info)) best@(i, list) =
                      case compare prio i of
                         LT -> best
                         EQ -> (i, (selname, (head es, info)):list)
                         GT -> (prio, [(selname, (head es, info))])
                   heuristicNames = map fst listWithBest
                   remainingEdges = map snd listWithBest
               case listWithBest of
                  [] -> do logMsg "Unfortunately, none of the heuristics could be applied"
                           rec edges rest
                  _  -> do logMsg ("Selected heuristics are " ++ unwords heuristicNames ++ ". "
                                   ++ shrunkAndFinalMsg edges remainingEdges)
                           logMsg ("   selected with priority "++show thePrio++": "++showSet (map fst remainingEdges)++"\n")
                           rec remainingEdges rest

evalSelector :: (MonadWriter LogEntries m, HasTypeGraph m info) => [(EdgeId, info)] -> Selector m info -> m [(Int, [EdgeId], info)]
evalSelector edges selector =
   case selector of

      Selector (name, f) ->
         do logMsg ("- "++name++" (selector)")
            let op list edge =
                   do x <- f edge
                      case x of
                         Nothing -> return list
                         Just (prio, string, es, info) ->
                            do logMsg ("     "++string++" (prio="++show prio++") => "++showSet es)
                               return ((prio, es, info) : list)
            foldM op [] edges

      SelectorList (name, f) ->
         do result <- f edges
            logMsg ("- "++name++" (list selector)")
            case result of
               Nothing -> return []
               Just (i,_,es,info) -> return [(i,es,info)]

showSet :: Show a => [a] -> String
showSet as = "{" ++ f (map show as) ++ "}"
   where f [] = ""
         f xs = foldr1 (\x y -> x++","++y)  (map show xs)

allErrorPaths :: HasTypeGraph m info => m (HeuristicInput info)
allErrorPaths =
   do is      <- getMarkedPossibleErrors
      cGraph  <- childrenGraph is
      let toCheck = nub $ concat (is : [ [a,b] | ((a,b),_) <- cGraph ])
      paths1  <- constantClashPaths toCheck
      paths2  <-  trace ("CONST CLASH PATH\n" ++ show (map flattenPath paths1) ++"\n\n\n") $    
        infiniteTypePaths cGraph
      let errorPath = reduceNumberOfPaths (simplifyPath (altList (paths1 ++ paths2)))
      expanded <- expandPath errorPath
      endpointInfo <- expandPathInclusive errorPath
      let
        edgeTform stg e =
          case Class.getEdgeCreator stg e of
            Nothing -> e
            Just x -> x
      -- creatorPath <- useTypeGraph $ \stg -> mapPath (edgeTform stg) expanded
      edgeList <- allEdges 
      let retVal = expanded --expanded :|: creatorPath
      -- return $ trace ("ALL ERR PATHS " ++ show expanded ++ "\n\nROOT ERR PATHS " ++ show creatorPath) $ retVal
      -- trace ("PRE EXPANSION " ++ show errorPath ++ "\nPOST " ++ show (fst <$> expanded)) $ 
      let creatorPair  e = do
                        c <- getEdgeCreator e
                        return $ case c of
                         Nothing -> (fst e, e)
                         Just cIn -> (fst e, cIn) 
      creatorPairs <- forM edgeList creatorPair  
      return $ HInput endpointInfo retVal edgeList (M.fromList creatorPairs)
----------------------------

-- not simplified: can also contain implied edges
constantClashPaths :: HasTypeGraph m info => [VertexId] -> m [TypeGraphPath info]
constantClashPaths []     = return []
constantClashPaths (first:rest) =
   do vertices <- verticesInGroupOf first
      let vs    = map fst vertices
          rest' = filter (`notElem` vs) rest
      pathInGroup vertices <++> constantClashPaths rest'

 where

  pathInGroup :: HasTypeGraph m info => [(VertexId, VertexInfo)] -> m [TypeGraphPath info]
  pathInGroup = errorPath . groupTheConstants . getConstants

  getConstants :: [(VertexId, VertexInfo)] -> [(VertexId, Constant)]
  getConstants vertices =
     [ (i, s  ) | (i, (VCon s  , _)) <- vertices ] ++
     [ (i, CApp) | (i, (VApp _ _, _)) <- vertices ]

  -- lists of vertex numbers with the same type constant
  -- (all vertices are in the same equivalence group)
  groupTheConstants :: [(VertexId, Constant)] -> [[VertexId]]
  groupTheConstants =
     sortBy (compare `on` length)
     .  map (map fst)
     .  groupBy ((==) `on` snd)
     .  sortBy  (compare `on` snd)

  errorPath :: HasTypeGraph m info => [[VertexId]] -> m [TypeGraphPath info]
  errorPath []        = return []
  errorPath [_]       = return []
  errorPath (is:iss) =
     let f i = allPathsList i (concat iss)
     in mapM f is <++> errorPath iss

----------------------------

-- not simplified: can also contain implied edges
infiniteTypePaths :: HasTypeGraph m info => ChildGraph -> m [TypeGraphPath info]
infiniteTypePaths cGraph =
   do pss <- mapM (makePathForInfiniteGroup . inThisGroup) allGroups
      return (concat pss)
      -- error (unlines $ map (show . inThisGroup) allGroups)

 where
   allGroups :: [[VertexId]]
   allGroups = infiniteGroups (map fst cGraph)

   -- puts the eqgroup with the least childedges to another group in front of the list
   inThisGroup :: [VertexId] -> ChildGraph
   inThisGroup infGroup =
      let p ((x, y), _) = (x `elem` infGroup) && (y `elem` infGroup)
          f (_, xs) (_, ys) = length xs `compare` length ys
      in sortBy f (filter p cGraph)

   makePathForInfiniteGroup :: HasTypeGraph m info => ChildGraph -> m [TypeGraphPath info]
   makePathForInfiniteGroup groupGraph =
      case groupGraph of
         [] -> return []
         (_, childEdges) : rest ->
            let g (x, y) = allSubPathsList (concatMap snd rest) y [x]
            in mapM g childEdges <++> infiniteTypePaths rest

type ChildGraph = [((VertexId, VertexId), [(VertexId, VertexId)])]

childrenGraph :: HasTypeGraph m info => [VertexId] -> m ChildGraph
childrenGraph = rec []
   where
      rec as []     = return as
      rec as (i:is) =
         do vertices <- verticesInGroupOf i
            ri       <- representativeInGroupOf i
            if ri `elem` map (fst . fst) as
              then rec as is
              else do let cs = concat [ [(n, l), (n, r)] | (n, (VApp l r, _)) <- vertices ]
                      cs' <- let f t = do r <- representativeInGroupOf (snd t)
                                          return (r, t)
                             in mapM f cs
                      let children = map (\((a,b):xs) -> (a,b:map snd xs))
                                   . groupBy ((==) `on` fst)
                                   . sortBy  (compare `on` fst)
                                   $ cs'
                      rec ([ ((ri, rc), xs) | (rc, xs) <- children ] ++ as) (map fst children ++ is)

infiniteGroups :: [(VertexId, VertexId)] -> [[VertexId]]
infiniteGroups xs =
   let representatives = nub (map fst xs ++ map snd xs)
       map1 = M.fromList (zip representatives [0..])
       f1 i = M.findWithDefault (internalError "Top.TypeGraph.ApplyHeuristics" "infiniteGroups" "error in lookup1 of makeMap") i map1
       map2 = M.fromList (zip [0..] representatives)
       f2 i = M.findWithDefault (internalError "Top.TypeGraph.ApplyHeuristics" "infiniteGroups" "error in lookup2 of makeMap") i map2
       edgeList = [ (f1 i, f1 c) | (i, c) <- xs ]
       graph    = buildG (0, length representatives - 1) edgeList
       groups   = map flatten (scc graph)
       selfRecursive = [ f1 i | (i, j) <- xs, i == j ]
       recursive = let p [i] = i `elem` selfRecursive
                       p is  = length is > 1
                   in map (map f2) (filter p groups)
   in recursive

allSubPathsList :: HasTypeGraph m info => [(VertexId, VertexId)] -> VertexId -> [VertexId] -> m (TypeGraphPath info)
allSubPathsList childList vertex targets = rec S.empty vertex
 where
   rec :: HasTypeGraph m info => S.Set VertexId -> VertexId -> m (TypeGraphPath info)
   rec without start =
      do vs <- verticesInGroupOf start
         if any (`elem` map fst vs) targets
            then sameGroup
            else otherGroup vs
    where
      -- targets are in the same group as the source
      sameGroup = do
         directPath <- allPathsListWithout without start targets
         return (simplifyPath directPath)

      -- go down to another equivalence group
      otherGroup vs = do
         extendedPaths <- mapM (recDown vs) (targetPairs vs)
         return (altList extendedPaths)

      recDown vs (newStart, childTargets) = do
         let newWithout = without `S.union` S.fromList (map fst vs){- don't return to this equivalence group -}
             f ct = let set = S.fromList [ t | t <- childTargets, t /= ct ]
                    in rec (set `S.union` newWithout) ct
         path     <- allPathsListWithout without start [newStart]
         newPaths <- mapM f childTargets
         return (path :+: altList newPaths)

      targetPairs :: [(VertexId, (VertexKind, Maybe Tm.VAL))] -> [(VertexId, [VertexId])]
      targetPairs vs =
         let p (i, j) =  i `elem` map fst vs
                         && not (i `S.member` without || j `S.member` without)
         in map (\((i,j):rest) -> (i, j:map snd rest))
            . groupBy ((==) `on` fst)
            . sortBy  (compare `on` fst)
            $ filter p childList

expandPath :: HasTypeGraph m info => TypeGraphPath info -> m (Path (EdgeId, info))
expandPath Fail = return Fail
expandPath p = --trace ("EXPANDING PATH" ++ show p ++ " with steps " ++ show (steps p)) $ 
   do 
      let impliedEdges = nub [ intPair (v1, v2) | (_, Implied _ (VertexId v1) (VertexId v2)) <- steps p ] 
      expandTable <- impliedEdgeTable impliedEdges

      let convert history path =
             case path of
                Empty -> Empty
                Fail  -> Fail
                p1 :+: p2 -> convert history p1 :+: convert history p2
                p1 :|: p2 -> convert history p1 :|: convert history p2
                Step (edge, edgeInfo) ->
                   case edgeInfo of
                      Initial info -> Step (edge, info)
                      Child _ -> Empty
                      Implied _ (VertexId v1) (VertexId v2)
                         | pair `S.member` history -> Empty
                         | otherwise ->
                              convert (S.insert pair history) (lookupPair expandTable pair)
                       where
                        pair = intPair (v1, v2)
      return (convert S.empty p)
      -- trace ("IMPLIED EDGES " ++ show impliedEdges ++    "\nPATH TABLE " ++ show expandTable) $ return ret

-- startVertex ((EdgeId a b _, info):(EdgeId a' b' _,_):_) = 
--   (if (a == a' || a == b') then b else a, info) 

-- endVertex p = startVertex (reverse p)

-- checkChild a b = useTypeGraph (Class.isChildOf a b)

-- fixPair (start, end, vid1, vid2) = do
--   startAnd1 <- checkChild vid1 start
--   startAnd2 <- checkChild vid2 start
--   endAnd1 <- checkChild vid1 end
--   endAnd2 <- checkChild vid2 end
--   return $
--         if startAnd1 && endAnd2
--           then (vid1, vid2)
--         else if startAnd2 && endAnd1
--           then (vid2, vid1)
--         else 
--           error $ "Child parent relation fail in Inclusive path\n"

unVertexId (VertexId v) = v
unVertexPair (x,y) = intPair (unVertexId x, unVertexId y)

firstEdges :: Path a -> [a]
firstEdges (p :+: q) = 
  let pedges = firstEdges p
  in if null pedges then firstEdges q else pedges
firstEdges (Step a) = [a]
firstEdges (p :|: q) = firstEdges p ++ firstEdges q
firstEdges _ = [] 

inflatePath :: [[a]] -> Path a
inflatePath = simplifyPath . altList . (map (seqList . (map Step)))

reversePath = inflatePath . (map reverse) . flattenPath

fixPath :: (Show info) => Path (EdgeId, info) -> Path (EdgeId, info)
fixPath = inflatePath . fixFlatPath . flattenPath

fixTypeGraphPath :: (Class.TypeGraph g info ) =>  TypeGraphPath info -> g -> TypeGraphPath info
fixTypeGraphPath p g = inflatePath $ (map (map fixImplied)) $ fixFlatPath $ flattenPath p
  where
    isChild a b = Class.isChildOf a b g
    fixImplied e@(EdgeId v1 v2 cnr, Implied x  u1 u2 ) = 
      if isChild u1 v1 && isChild u2 v2 then e 
      else if isChild u2 v1 && isChild u1 v2 then (EdgeId v1 v2 cnr, Implied x u2 u1)
      else (error $ "Bad Implied edge " ++ show e) 
    fixImplied x = x

fixFlatPath :: (Show info) => [[(EdgeId, info)]] -> [[(EdgeId, info)]]
fixFlatPath = map (helper [])
  where 
    helper accum [] = reverse accum
    helper accum [e] = helper (e:accum) []
    helper accum l@(e@(EdgeId v1 v2 cnr, i) : e2@(EdgeId u1 u2 _, _): rest) = 
      if (v1 `elem` [u1, u2])
        then helper ((EdgeId v2 v1 cnr, i):accum) (e2: rest)
      else if (v2 `elem` [u1, u2]) 
        then helper (e:accum) (e2:rest)
      else (error $ "fixPath, disconnected edge" ++ show accum ++ show l) 


expandPathInclusive :: forall m info . HasTypeGraph m info => TypeGraphPath info -> m (EndpointInfo info)
expandPathInclusive Fail = return []
expandPathInclusive  badPath = --trace ("EXPANDING PATH" ++ show p ++ " with steps " ++ show (steps p)) $ 
    do       
      p <- useTypeGraph (fixTypeGraphPath badPath)
      let impliedEdges = nub [ intPair (v1, v2) | (_, Implied _ (VertexId v1) (VertexId v2)) <- steps p ]
      expandTable <- impliedEdgeTable impliedEdges
      let convert :: (S.Set IntPair) -> TypeGraphPath info -> m (Path (EdgeId, [info]), [info], [info])
          convert history path =
              case path of
                Empty -> return (Empty, [], [])
                Fail  -> return (Fail, [], [])
                p1 :+: p2 -> do 
                    (p1', s, _) <- convert history p1
                    (p2', _, e) <- convert history p2
                    return (p1' :+: p2', s, e) 
                p1 :|: p2 -> do 
                    (p1', s1, e1) <- convert history p1
                    (p2', s2, e2) <- convert history p2
                    return (p1' :|: p2',  (s1 ++ s2), (e1 ++ e2)) 
                Step (edge@(EdgeId start end cnr ), edgeInfo) ->
                    case edgeInfo of
                      Initial localInfo -> return (Step (edge, [localInfo]), [localInfo], [localInfo])
                      Child _ -> return (Empty, [], [])
                      Implied _ vid1@(VertexId v1) vid2@(VertexId v2) -> do
                          -- asbe@(afterStart, beforeEnd) <- fixPair (start, end, vid1, vid2)
                          let pair = intPair (v1, v2)
                          case () of
                            _
                              | pair `S.member` history -> return (Empty, [], [])
                              | otherwise -> do
                                  let pairPath = (lookupPair expandTable pair)
                                  (subPath, startInfo, endInfo) <- convert (S.insert pair history) pairPath
                                   
                                  let e1 = -- trace ("SUBPATH " ++ show (fst <$> subPath) ++ " from " ++ show edge ++ " PATH " ++ show pairPath) $ 
                                          Step (EdgeId start vid1 cnr, startInfo)
                                  let e2 = Step (EdgeId vid2 end cnr, endInfo)
                                  -- trace ("CONVERT " ++ show edge ++ " joined by " ++ show (vid1, vid2) ++ " INTO " ++ show (fst <$> e1, fst <$> subPath, fst <$> e2)) $ 
                                  return (e1 :+: subPath :+: e2, startInfo, endInfo)
                        where
                          
      (ret, _, _) <- (convert S.empty p)
      let flattened = flattenPath $ fixPath ret
          endPoints = [ x | p <- flattened, (EdgeId start _ _ , info1) <- [head p], (EdgeId _ end _, info2) <- [last p], x <- [(start, info1), (end, info2)]]
      trace ("EXPANDED FULL" ++ show (flattenPath ret)  ++ "\nENDPOINTS: " ++ show endPoints) $ 
        forM endPoints $ \(p,info) -> do
          v <- typeFromTermGraph p
          return (v, info)


impliedEdgeTable :: HasTypeGraph m info => [IntPair] -> m (PathMap info)
impliedEdgeTable = insertPairs M.empty
 where
   insertPairs fm [] = return fm
   insertPairs fm (pair:rest)
      | pair `M.member` fm = insertPairs fm rest
      | otherwise = do
              let (i1, i2) = tupleFromIntPair pair
              badPath <- allPaths (VertexId i1) (VertexId i2)
              fixedPath <- useTypeGraph $ fixTypeGraphPath badPath
              let flat = flattenPath fixedPath
              let headVerts = [v | Just (EdgeId v1 v2 _, _) <- (map listToMaybe flat), (VertexId v) <- [v1, v2]]
              let 
                revPath = 
                  if i1 `elem` headVerts then  flat 
                  else if i2 `elem` headVerts then  (map reverse flat) 
                  else error "Neither vertex is in our head vertices"
              let path =  inflatePath revPath
              let new = nub [ intPair (v1, v2) | (_, Implied _ (VertexId v1) (VertexId v2)) <- steps path ]
              insertPairs ( M.insert pair path fm) (rest `union` new)

-------------------------------
--

newtype IntPair = HiddenIP { tupleFromIntPair :: (Tm.Nom, Tm.Nom) }

intPair :: (Tm.Nom, Tm.Nom) -> IntPair
intPair (x, y) = HiddenIP (x,y)
  --  | x <= y    = HiddenIP (x, y)
  --  | otherwise = HiddenIP (y, x)

instance Show IntPair where
   show (HiddenIP pair) = show pair

instance Eq IntPair where
   HiddenIP pair1 == HiddenIP pair2 =
      pair1 == pair2

instance Ord IntPair where
   HiddenIP pair1 `compare` HiddenIP pair2 =
      pair1 `compare` pair2

type PathMap info = M.Map IntPair (Path (EdgeId, PathStep info))

lookupPair :: PathMap info -> IntPair -> Path (EdgeId, PathStep info)
lookupPair fm pair =
   let err = internalError "Top.TypeGraph.ApplyHeuristics" "lookupPair" "could not find implied edge while expanding"
   in M.findWithDefault err pair fm

-- -- move to another module
-- predicatePath :: ({-HasQual m info,-} HasTypeGraph m info) => m (Path (EdgeId, PathStep info))
-- predicatePath =
--    do ps       <- allQualifiers
--       simples  <- simplePredicates ps
--       makeList S.empty Empty simples
 --
 -- where
 --  simplePredicates ps =
 --     do classEnv <- getClassEnvironment
 --        syns     <- getTypeSynonyms
 --        let reduced = fst (contextReduction syns classEnv ps)
 --        return [ (s, VertexId i) | Predicate s (TVar i) <- reduced ]
 --
 --  makeList history path pairs =
 --     do xs <- mapM (make history path) pairs
 --        return (altList xs)
 --
 --  make history path (pClass, i)
 --     | i `S.member` history = return Fail
 --     | otherwise =
 --          do classEnv <- getClassEnvironment
 --             syns     <- getTypeSynonyms
 --             vertices <- verticesInGroupOf i
 --
 --             -- vertices to inspect
 --             let constants  = [ (vid, TCon s) | (vid, (VCon s, _)) <- vertices ]
 --             applys <- let f i' = do tp <- typeFromTermGraph i'
 --                                     return (i', tp)
 --                       in mapM f [ i' | (i', (VApp _ _, _)) <- vertices ]
 --
 --             let f (vid, tp)
 --                    | null errs = -- everything is okay: recursive call
 --                         do let -- don't visit these vertices
 --                                donts = S.fromList [ VertexId j | j <- ftv (map snd applys), j `notElem` ftv tp ]
 --                            path'   <- allPathsListWithout history i [vid]
 --                            simples <- simplePredicates reduced
 --                            makeList (donts `S.union` newHistory) (path :+: path') simples
 --
 --                    | otherwise = -- this is an error path
 --                         do path' <- allPathsListWithout history i [vid]
 --                            return (path :+: path')
 --
 --                  where (reduced, errs) = contextReduction syns classEnv [Predicate pClass tp]
 --                        newHistory      = S.fromList (map fst vertices) `S.union` history
 --
 --             xs <- mapM f (constants ++ applys)
 --             return (altList xs)
