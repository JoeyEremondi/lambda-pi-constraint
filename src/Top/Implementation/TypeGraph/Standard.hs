{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Top.Implementation.TypeGraph.Standard where

import Data.List (nub)
import qualified Data.Map as M
import Data.Maybe
import qualified PatternUnify.Tm as Tm
import Top.Implementation.General
import Top.Implementation.TypeGraph.Basics
import Top.Implementation.TypeGraph.Class
import Top.Implementation.TypeGraph.EquivalenceGroup
import Top.Types
import qualified Unbound.Generics.LocallyNameless as Ln
import Utils (internalError)

import Data.Foldable (foldlM)

--import Debug.Trace (trace)

data StandardTypeGraph info = STG
   { referenceMap            :: M.Map VertexId Int{- group number -}
   , equivalenceGroupMap     :: M.Map Int (EquivalenceGroup info)
   , equivalenceGroupCounter :: Int
   , possibleErrors          :: [VertexId]
   , constraintNumber        :: Tm.Nom
   }

instance Show info => Empty (StandardTypeGraph info) where
   empty = STG
      { referenceMap            = M.empty
      , equivalenceGroupMap     = M.empty
      , equivalenceGroupCounter = 0
      , possibleErrors          = []
      , constraintNumber        = Ln.s2n "constr"
      }

instance Show (StandardTypeGraph info) where
   show stg =
      "(Type graph consists of " ++ show (M.size (equivalenceGroupMap stg)) ++ " equivalence groups)"



-- addElim subs original unique (Tm.Elim can args) g0 =
addElim :: (Ln.Fresh m, TypeGraph graph info) => Tm.Subs -> Maybe Tm.VAL -> Tm.Nom -> Tm.Elim -> graph -> m (VertexId, graph)
addElim subs original unique (Tm.Elim can args) g0 = do
  let vinit = VertexId unique
  let initVal = (vinit, addVertex vinit (VCon $ ConElim can, original) g0)
  let
    foldFn (vlast, glast) ctorArg = do
      (vnew, subGraph) <- addTermGraph subs unique ctorArg glast
      vid <- VertexId <$> Ln.fresh unique
      return
       ( vid
       , addVertex vid (VApp vlast vnew, original) subGraph)
  foldlM foldFn initVal args

addHead :: (Ln.Fresh m, TypeGraph graph info) => Maybe Tm.VAL -> Tm.Nom -> Tm.Head -> graph -> m (VertexId, graph)
addHead original unique (Tm.Var nm _) stg = do--TODO handle twins?
  vinit <- VertexId <$> Ln.fresh unique
  --ourFresh <- Ln.fresh unique
  return (vinit, addVertex vinit (VCon $ BoundVar nm, original) stg)
--Metavariables are indexed by their names
addHead original unique (Tm.Meta nm) stg =
  let
    vinit = VertexId nm
  in
    return (vinit, addVertex vinit (VVar, original) stg)


instance TypeGraph (StandardTypeGraph info) info where
   addTermGraph synonyms unique tp stg =
         let
           evaldType :: Tm.VAL
           evaldType = Ln.runFreshM $ Tm.eval synonyms tp
           (newtp, original) = (evaldType, Just tp)
                -- case expandToplevelTC synonyms tp of
                --    Nothing -> (tp, Nothing)
                --    Just x  -> (x, Just tp)
         in case newtp of
               Tm.C ctor args -> do
                   fresh1 <- Ln.fresh unique
                   vinit <- VertexId <$> Ln.fresh unique
                   let

                       initVal = (vinit, addVertex vinit (VCon $ Con ctor, original) stg)
                       foldFn (vlast, glast) ctorArg = do
                         (vnew, subGraph) <- addTermGraph synonyms unique ctorArg glast
                         vid <- VertexId <$> Ln.fresh unique
                         return ( vid
                          , addVertex vid (VApp vlast vnew, original) subGraph)

                   foldlM foldFn initVal args

                --Insert function application
               Tm.N hd elims -> do
                  vinit <- VertexId <$> Ln.fresh unique
                  initVal <- addHead original unique hd stg
                  let foldFn (vlast, glast) elim = do
                        (vnew, subGraph) <- addElim synonyms original unique elim glast
                        vid <-  VertexId <$> Ln.fresh unique
                        return
                         ( vid
                         , addVertex vid (VElim vlast vnew, original) subGraph)
                  foldlM foldFn initVal elims
               Tm.L bnd -> do
                  (nm, body) <- Ln.unbind bnd
                  (vbody, subGraph1) <- addTermGraph synonyms unique body stg
                  (vparam, subGraph2) <- addTermGraph synonyms unique (Tm.var nm) subGraph1
                  vid <- VertexId <$> Ln.fresh unique
                  return
                   ( vid
                   , addVertex vid (VLam vparam vbody, original) subGraph2)



   addVertex v info =
      createGroup (insertVertex v info emptyGroup)

   addEdge edge@(EdgeId v1 v2 _) info =
      propagateEquality v1 . updateGroupOf v1 (insertEdge edge info) . combineClasses [v1, v2]

   addNewEdge (v1, v2) info stg = do
      let cnr = makeEdgeNr (constraintNumber stg)
      ourFresh <- Ln.fresh $ constraintNumber stg
      return $ addEdge (EdgeId v1 v2 cnr) info (stg { constraintNumber = ourFresh})

   deleteEdge edge@(EdgeId v1 _ _) =
      propagateRemoval v1 . updateGroupOf v1 (removeEdge edge)

   verticesInGroupOf i =
      vertices . getGroupOf i

   substituteTypeSafe synonyms =
      let
          rec :: [Tm.Nom] -> Tm.VAL -> StandardTypeGraph info -> Maybe Tm.VAL
          rec history (Tm.N hd []) stg
            |  (Tm.headVar hd) `elem` history  = Nothing
            |  otherwise         =
                  case maybeGetGroupOf (VertexId (Tm.headVar hd)) stg of
                     Nothing ->
                        Just (Tm.N hd [])
                     Just _ ->
                        do newtp <- typeOfGroup synonyms (getGroupOf (VertexId (Tm.headVar hd)) stg)
                           case newtp of
                              vval@(Tm.N hdj [])  -> Just vval -- (Tm.headVar hdj)
                              _      -> rec ((Tm.headVar hd):history) newtp stg

          rec _ tp@(Tm.C con []) _ = Just tp

          rec history (Tm.C con argList) stg =
            Tm.C con <$> mapM (\arg -> rec history arg stg) argList
       in rec []

   edgesFrom i =
      let p (EdgeId v1 v2 _, _) = v1 == i || v2 == i
      in filter p . edges . getGroupOf i

   allPathsListWithout without v1 vs =
      equalPaths without v1 vs . getGroupOf v1

   makeSubstitution syns stg =
      let f eqgroup =
             case typeOfGroup syns eqgroup of
                Just tp -> [ (vid, tp) | (vid@(VertexId i), _) <- vertices eqgroup, notId i tp ]
                Nothing -> internalError "Top.TypeGraph.Implementation" "makeSubstitution" "inconsistent equivalence group"
          notId i (Tm.N h []) = i /= (Tm.headVar h)
          notId _ _        = True
      in concatMap f (getAllGroups stg)

   typeFromTermGraph vid stg =
      case [ tp | (x, (tp, _)) <- verticesInGroupOf vid stg, vid == x ] of
         [VCon (Con s)]   -> Tm.C s []
         [VCon (ConElim s)]   -> error "ConElim from term graph"
         [VApp a b] ->
           case typeFromTermGraph a stg of
             (Tm.C ctor args) ->
                Tm.C ctor $ args ++ [typeFromTermGraph b stg]
         _          -> vertexIdToTp vid

   markAsPossibleError     =
      addPossibleInconsistentGroup

   getMarkedPossibleErrors =
      getPossibleInconsistentGroups

   unmarkPossibleErrors =
      setPossibleInconsistentGroups []

   toDot g =
     let
       eqGroups = M.elems $ equivalenceGroupMap g
       nodePairs = concatMap vertices eqGroups
       theEdges = [(v1, v2) | (EdgeId v1 v2 _,_) <- concatMap (edges) eqGroups]

       dotLabel :: VertexId -> VertexInfo -> (String)
       dotLabel vid (VVar,_) = "Meta " ++ show vid
       dotLabel vid ((VCon k),_) = show k
       dotLabel vid (VApp _ _, Just tm) = "App " ++ show vid ++ " " ++ Tm.prettyString tm
       dotLabel vid (VLam _ _, Just tm) = "Lam " ++ show vid ++ " " ++ Tm.prettyString tm
       dotLabel vid (VElim _ _, Just tm) = "Elim " ++ show vid ++ " " ++ Tm.prettyString tm

       dotLabel vid _ = show vid

       dotEdges :: VertexId -> VertexInfo -> (String)
       dotEdges vid (VVar,_) = ("")
       dotEdges vid ((VCon k),_) = ("")
       dotEdges vid ((VLam k1 k2),_) =
         (show vid ++ " -> " ++ show k1 ++ " [style = dashed, label = \"L\"];//1\n"
           ++ show vid ++ " -> " ++ show k2 ++ " [style = dashed, label = \"R\"];//2\n")
       dotEdges vid ((VApp k1 k2),_) =
         (show vid ++ " -> " ++ show k1  ++ " [style = dashed, label = \"L\"];//3\n"
           ++ show vid ++ " -> " ++ show k2 ++ " [style = dashed, label = \"R\"];//4\n")
       dotEdges vid ((VElim k1 k2),_) =
         (show vid ++ " -> " ++ show k1 ++ " [style = dashed, label = \"L\"];//5\n"
           ++ show vid ++ " -> " ++ show k2 ++ " [style = dashed, label = \"R\"];//6\n")

       termEdges = map (uncurry dotEdges) nodePairs

       nodeDecls =
        [show v ++ " [label = \"" ++ show v ++ ": " ++ dotLabel v vinfo ++ "\" ];\n" | (v, vinfo) <- nodePairs ]
        --[show num ++ " [label = \"" ++ s ++ "\" ];\n" | s <- termNames ]
       edgeDecls =
          [show n1 ++ " -> " ++ show n2 ++ " [dir=none] ;\n" | (n1, n2) <- theEdges ]


     in "digraph G\n{\n" ++ concat (nodeDecls) ++ concat (edgeDecls ++ termEdges) ++ "\n}"

-- Helper functions
combineClasses :: [VertexId] -> StandardTypeGraph info -> StandardTypeGraph info
combineClasses is stg =
      case nub (map (`representativeInGroupOf` stg) is) of
         list@(i:_:_) ->
            let eqgroups = map (`getGroupOf` stg) list
                newGroup = foldr combineGroups emptyGroup eqgroups
            in addPossibleInconsistentGroup i . createGroup newGroup . foldr removeGroup stg $ eqgroups
         _ -> stg

propagateEquality :: VertexId -> StandardTypeGraph info -> StandardTypeGraph info
propagateEquality vid stg =
   let (listLeft, listRight) = childrenInGroupOf vid stg
       left  = map (flip representativeInGroupOf stg . child) listLeft
       right = map (flip representativeInGroupOf stg . child) listRight
   in (if length (nub right) > 1
         then propagateEquality (head right)
         else id)
    . (if length (nub left) > 1
         then propagateEquality (head left)
         else id)
    . (if length listLeft > 1
         then addClique (makeClique listRight) . addClique (makeClique listLeft)
         else id)
    $ stg

addClique :: Clique -> StandardTypeGraph info -> StandardTypeGraph info
addClique clique =
   updateGroupOf (cliqueRepresentative clique) (insertClique clique) . combineClasses (childrenInClique clique)

propagateRemoval :: VertexId -> StandardTypeGraph info -> StandardTypeGraph info
propagateRemoval i stg =
   let (is, new) = splitClass i stg
       ts = map (`childrenInGroupOf` new) is

       (leftList, rightList) = unzip ts
       cliqueLeft  = makeClique (concat leftList)
       cliqueRight = makeClique (concat rightList)
       newCliques  = [ makeClique list | list <- leftList ++ rightList, length list > 1 ]
       children    = [ child pc | pc:_ <- leftList ++ rightList ]
   in
      if length (filter (not . null) leftList) > 1
        then flip (foldr propagateRemoval) children
           . flip (foldr addClique) newCliques
           . deleteClique cliqueRight
           . deleteClique cliqueLeft
           $ new
        else new

splitClass ::  VertexId -> StandardTypeGraph info -> ([VertexId], StandardTypeGraph info)
splitClass vid stg =
   let eqgroup   = getGroupOf vid stg
       newGroups = splitGroup eqgroup
       results   = [ vid2 | (vid2, _):_ <- map vertices newGroups ]
       newGraph
          | length newGroups > 1 = foldr createGroup (removeGroup eqgroup stg) newGroups
          | otherwise = stg
   in (results, newGraph)

deleteClique :: Clique -> StandardTypeGraph info -> StandardTypeGraph info
deleteClique clique =
   updateGroupOf (cliqueRepresentative clique) (removeClique clique)

-----------------------------------------------------------------

createGroup :: EquivalenceGroup info -> StandardTypeGraph info -> StandardTypeGraph info
createGroup eqgroup stg =
   let newGroupNumber = equivalenceGroupCounter stg
       list = [(i, newGroupNumber) | (i, _) <- vertices eqgroup ]
   in if null list
        then internalError "Top.TypeGraph.TypeGraphMonad" "createNewGroup" "cannot create an empty equivalence group"
        else stg { referenceMap            = referenceMap stg `M.union` M.fromList list
                 , equivalenceGroupMap     = M.insert newGroupNumber eqgroup (equivalenceGroupMap stg)
                 , equivalenceGroupCounter = newGroupNumber + 1
                 }

removeGroup :: EquivalenceGroup info -> StandardTypeGraph info -> StandardTypeGraph info
removeGroup eqgroup stg =
   let vertexIds   = map fst (vertices eqgroup)
       oldGroupNr  = maybeToList (M.lookup (head vertexIds) (referenceMap stg))
   in stg { referenceMap        = foldr M.delete (referenceMap stg) vertexIds
          , equivalenceGroupMap = foldr M.delete (equivalenceGroupMap stg) oldGroupNr
          }

updateGroupOf :: VertexId -> (EquivalenceGroup info -> EquivalenceGroup info) -> StandardTypeGraph info -> StandardTypeGraph info
updateGroupOf vid f stg =
   let eqgrp = getGroupOf vid stg
       err  = internalError "Top.TypeGraph.TypeGraphMonad" "updateEquivalenceGroupOf" ("error in lookup map: "++show vid)
       eqnr = M.findWithDefault err vid (referenceMap stg)
   in stg { equivalenceGroupMap = M.insert eqnr (f eqgrp) (equivalenceGroupMap stg) }

maybeGetGroupOf :: VertexId -> StandardTypeGraph info -> Maybe (EquivalenceGroup info)
maybeGetGroupOf vid stg =
   do eqnr <- M.lookup vid (referenceMap stg)
      let err = internalError "Top.TypeGraph.TypeGraphMonad" "equivalenceGroupOf" "error in lookup map"
      return (M.findWithDefault err eqnr (equivalenceGroupMap stg))

getGroupOf :: VertexId -> StandardTypeGraph info -> EquivalenceGroup info
getGroupOf vid =
   let err = internalError "Top.TypeGraph.Standard" "getGroupOf" ("the function getGroupOf does no longer create an empty group if the vertexId " ++ show vid ++ " doesn't exist")
   in fromMaybe err . maybeGetGroupOf vid

getAllGroups :: StandardTypeGraph info -> [EquivalenceGroup info]
getAllGroups = M.elems . equivalenceGroupMap

vertexExists :: VertexId -> StandardTypeGraph info -> Bool
vertexExists vid = isJust . M.lookup vid . referenceMap

-----------------------------------------------------------------------------------

getPossibleInconsistentGroups :: StandardTypeGraph info -> [VertexId]
getPossibleInconsistentGroups = possibleErrors

setPossibleInconsistentGroups :: [VertexId] -> StandardTypeGraph info -> StandardTypeGraph info
setPossibleInconsistentGroups vids stg = stg { possibleErrors = vids }

addPossibleInconsistentGroup :: VertexId -> StandardTypeGraph info -> StandardTypeGraph info
addPossibleInconsistentGroup vid stg = stg { possibleErrors = vid : possibleErrors stg }




-- addTermGraphM :: (Ln.Fresh m) => Tm.Subs -> Tm.Nom -> Tm.VAL -> StandardTypeGraph info -> m (Tm.Nom, VertexId, StandardTypeGraph info)
-- addTermGraphM synonyms unique tp stg =
--       let
--         evaldType :: Tm.VAL
--         evaldType = Ln.runFreshM $ Tm.eval synonyms tp
--         (newtp, original) = (evaldType, Just tp)
--              -- case expandToplevelTC synonyms tp of
--              --    Nothing -> (tp, Nothing)
--              --    Just x  -> (x, Just tp)
--       in case newtp of
--             Tm.C ctor args -> do
--                 let
--                     vinit = VertexId unique
--                     initVal = (mkFresh unique, vinit, addVertex vinit (VCon ctor, original) stg)
--                     foldFn (ulast, vlast, glast) ctorArg = do
--                       (unew, vnew, subGraph) <- addTermGraphM synonyms ulast ctorArg glast
--                       myFresh <- Ln.fresh unew
--                       let vid = VertexId unew
--                       return ( myFresh
--                        , vid
--                        , addVertex vid (VApp vlast vnew, original) subGraph)
--
--                 foldlM foldFn initVal args
--
--              --Insert function application
--             Tm.N hd elims -> do
--                let
--                    vinit = VertexId unique
--                    initVal = addHead original unique hd stg
--                    foldFn (ulast, vlast, glast) elim = do
--                      let
--                         (unew, vnew, subGraph) = addElim synonyms original ulast elim glast
--                         vid = VertexId unew
--                      return
--                       ( mkFresh unew
--                       , vid
--                       , addVertex vid (VElim vlast vnew, original) subGraph)
--                foldlM foldFn initVal elims
--------------------------------------------------------------------------------
{-
setHeuristics :: [Heuristic info] -> StandardTypeGraph info -> StandardTypeGraph info
setHeuristics = setPathHeuristics . const

setPathHeuristics :: (Path (EdgeId, info) -> [Heuristic info]) -> StandardTypeGraph info -> StandardTypeGraph info
setPathHeuristics f stg = stg {typegraphHeuristics = f}

getPathHeuristics :: StandardTypeGraph info -> Path (EdgeId, info) -> [Heuristic info]
getPathHeuristics = typegraphHeuristics -}

addEqn
  :: (Ln.Fresh m)
  => info -> (Tm.VAL, Tm.VAL)
  -> StandardTypeGraph info
  -> m (StandardTypeGraph info)
addEqn info (v1, v2) stg = do
    (var1, g1) <-  addTermGraph M.empty (Ln.s2n "node") v1 stg
    (var2, g2) <-  addTermGraph M.empty (Ln.s2n "node") v2 g1
    --edgeNr <- Ln.fresh $ Ln.s2n "edge"
    --let ourEdge = EdgeId var1 var2 $ EdgeNrX edgeNr
    addNewEdge (var1, var2) info g2
