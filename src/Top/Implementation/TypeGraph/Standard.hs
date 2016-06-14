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
import qualified Data.List as List
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

import Data.Foldable (foldlM, foldrM)

import PatternUnify.ConstraintInfo as Info

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe

import Debug.Trace (trace)

type Info = Info.ConstraintInfo

--import Debug.Trace (trace)

data StandardTypeGraph = STG
   { referenceMap            :: M.Map VertexId Int{- group number -}
   , equivalenceGroupMap     :: M.Map Int (EquivalenceGroup Info)
   , equivalenceGroupCounter :: Int
   , possibleErrors          :: [VertexId]
   , constraintNumber        :: Tm.Nom
   , choiceEdges             :: [(Tm.CUID, VertexId)]
   , termNodes               :: M.Map Tm.Nom [(VertexId, Tm.VAL)]
   , collectedUpdates        :: M.Map Tm.Nom (Tm.VAL, (Tm.VAL, Tm.VAL) -> Info)
   }

instance Empty (StandardTypeGraph ) where
   empty = STG
      { referenceMap            = M.empty
      , equivalenceGroupMap     = M.empty
      , equivalenceGroupCounter = 0
      , possibleErrors          = []
      , constraintNumber        = Ln.s2n "constr"
      , choiceEdges = []
      , termNodes = M.empty
      , collectedUpdates = M.empty
      }

instance Show (StandardTypeGraph) where
   show stg =
      "(Type graph consists of " ++ show (M.size (equivalenceGroupMap stg)) ++ " equivalence groups)"





addCollectedUpdates :: (Ln.Fresh m) => VertexId -> Tm.VAL -> StandardTypeGraph -> m StandardTypeGraph
addCollectedUpdates vid oldVal stg =
  foldrM foldFun stg (Tm.fmvs oldVal)
    where
      foldFun alpha g =
        case M.lookup alpha (collectedUpdates g) of
          Nothing -> return g
          Just (alphaVal, info) -> do
            let newVal = Ln.subst alpha alphaVal oldVal
            addUpdateEdge vid (info) oldVal newVal g


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

addTermVert :: VertexId -> Tm.VAL -> M.Map Tm.Nom [(VertexId, Tm.VAL)] -> M.Map Tm.Nom [(VertexId, Tm.VAL)]
addTermVert vid t oldDict =
  let
    alphas = Tm.fmvs t
    foldFn alpha d =
      case M.lookup alpha d of
        Nothing -> M.insert alpha [(vid,t)] d
        Just oldList -> M.insert alpha ((vid,t):oldList) d
  in
    foldr foldFn oldDict alphas


instance TypeGraph (StandardTypeGraph) Info where

   getEdgeCreator = initialCreator

   addTermGraph synonyms unique tp stg =
         let
           evaldType :: Tm.VAL
           evaldType = Ln.runFreshM $ Tm.eval synonyms tp
           (newtp, original) = (evaldType, Just tp)
                -- case expandToplevelTC synonyms tp of
                --    Nothing -> (tp, Nothing)
                --    Just x  -> (x, Just tp)
         in case newtp of
               --TODO use meta as central node?
               Tm.VBot _ -> do
                 vinit <- VertexId <$> Ln.fresh unique
                 return (vinit, addVertex vinit (VertBot, original) stg)
               Tm.VChoice cid cuid alpha s t ->
                 --Just ignore second half of choice, edge to variable
                 --added when choice was generated
                 addTermGraph synonyms unique s stg
              --  do
              --    (vs, g1) <- addTermGraph synonyms unique s stg
              --    (vt, g2) <- addTermGraph synonyms unique t g1
              --    let allChoices = choiceEdges g2
              --    case List.lookup cuid allChoices of
              --       Nothing -> do
              --         choiceIntermediate <- Ln.fresh $ Ln.s2n $ "_choice_" ++ show (Tm.choiceIdToName cid)
              --         (vc, gInter1) <- addHead Nothing unique (Tm.Meta $ choiceIntermediate) g2
               --
              --         --Add this choice and mark it as added
              --         --gInter2 <- addNewEdge (vs, vc) (Info.choiceInfo (Tm.choiceRegion cid) Info.LeftChoice alpha s t) gInter1
              --         --gRet <- addNewEdge (vt, vc) (Info.choiceInfo (Tm.choiceRegion cid) Info.RightChoice alpha s t) gInter2
              --         let gRet = gInter1
              --         return (vc, gRet {choiceEdges = (cuid, vc) : allChoices})
               --
              --       Just vc -> return (vc, g2)
              --    --TODO representative vertex?


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

               --We can treat a lone meta or program variable as a node
               Tm.N hd [] ->
                 addHead original unique hd stg

               tm -> do
                 newVertex <- VertexId <$> Ln.fresh unique
                 cBot <- Tm.containsBottom tm
                 g1 <-
                    case (Tm.fmvs tm, cBot) of
                      ([], Nothing) -> do
                        vo <- Tm.makeOrdered tm
                        return (addVertex newVertex (VCon (NeutralTerm vo), Just tm) stg)
                      _ ->
                        return (addVertex newVertex (VTerm, Just tm) stg)
                 let g2 = g1 {termNodes = addTermVert newVertex tm (termNodes g1)}
                 gRet <- addCollectedUpdates newVertex tm g2
                 return (newVertex, gRet)


              --   --Insert function application
              --  Tm.N hd elims -> do
              --     vinit <- VertexId <$> Ln.fresh unique
              --     initVal <- addHead original unique hd stg
              --     let foldFn (vlast, glast) elim = do
              --           (vnew, subGraph) <- addElim synonyms original unique elim glast
              --           vid <-  VertexId <$> Ln.fresh unique
              --           return
              --            ( vid
              --            , addVertex vid (VElim vlast vnew, original) subGraph)
              --     foldlM foldFn initVal elims
              --  Tm.L bnd -> do
              --     (nm, body) <- Ln.unbind bnd
              --     (vbody, subGraph1) <- addTermGraph synonyms unique body stg
              --     (vparam, subGraph2) <- addTermGraph synonyms unique (Tm.var nm) subGraph1
              --     vid <- VertexId <$> Ln.fresh unique
              --     return
              --      ( vid
              --      , addVertex vid (VLam vparam vbody, original) subGraph2)

   allEdges stg =
     concatMap edges $ M.elems $ equivalenceGroupMap stg

   addVertex v info =
      createGroup (insertVertex v info emptyGroup)

   addEdge edge@(EdgeId v1 v2 _) info =
      propagateEquality v1 . updateGroupOf v1 (insertEdge edge info) . combineClasses [v1, v2]

   addNewEdge (v1, v2) info stg = do
      let cnr = makeEdgeNr (constraintNumber stg)
      ourFresh <- Ln.fresh $ constraintNumber stg
      return $ addEdge (EdgeId v1 v2 cnr) info (stg { constraintNumber = ourFresh})

   deleteEdge edge@(EdgeId v1 _ _) =
      removeDerived edge . propagateRemoval v1 . updateGroupOf v1 (removeEdge edge)

   verticesInGroupOf i =
      vertices . getGroupOf i

   substituteTypeSafe synonyms v g =
      let
          recElim history (Tm.Elim con vals) stg =
            Tm.Elim con <$> mapM  (\arg -> rec history arg stg) vals

          rec :: [Tm.Nom] -> Tm.VAL -> StandardTypeGraph -> Ln.FreshMT Maybe Tm.VAL
          rec history (Tm.N hd elims) stg
            |  (Tm.headVar hd) `elem` history  = trace "STS Head in history" $ lift Nothing
            |  otherwise         =
                  case maybeGetGroupOf (VertexId (Tm.headVar hd)) stg of
                     Nothing -> do
                        newElims <- mapM (\arg -> recElim history arg stg) elims
                        return (Tm.N hd newElims)
                     Just _ ->
                        do newHead <- lift $ typeOfGroup synonyms (getGroupOf (VertexId (Tm.headVar hd)) stg)
                           newElims <- mapM (\arg -> recElim history arg stg) elims
                           case newHead of
                              vval@(Tm.N hdj [])  ->  vval Tm.%%% newElims  -- (Tm.headVar hdj)
                              _     -> do
                                newVal <- newHead Tm.%%% newElims
                                rec ((Tm.headVar hd):history) newVal stg

          rec history (Tm.C con argList) stg =
            Tm.C con <$> mapM (\arg -> rec history arg stg) argList

          rec history (Tm.L bnd) stg = do
            (x, body) <- Ln.unbind bnd
            newBody <- rec history body stg
            return $ Tm.L $ Ln.bind x newBody

          rec _ tm _ = error $  "Sub type safe" ++ show tm
       in Ln.runFreshMT $ rec [] v g

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

   toDot g = toDotGen (M.elems $ equivalenceGroupMap g) g

   errorDot edges g =
    let
      verts = List.nub $ concatMap (\(EdgeId v1 v2 _) -> map (flip representativeInGroupOf $ g) [v1,v2]) edges
      groups = map (flip getGroupOf $ g) verts
    in toDotGen groups g


toDotGen eqGroups g =
     let
       --TODO keep singletons? just makes graph easier to read
       --filter ((> 1) . length . vertices) $

       nodePairs = concatMap vertices eqGroups
       theEdges = [(v1, v2, info) | (EdgeId v1 v2 _,info) <- List.nub $ concatMap (edges) eqGroups]

       dotLabel :: VertexId -> VertexInfo -> (String)
       dotLabel vid (VertBot,_) = "Bottom"
       dotLabel vid (VVar,_) = "Meta " ++ show vid
       dotLabel vid ((VCon k),_) = show k
       dotLabel vid (VApp _ _, Just tm) = "App " ++ show vid ++ " " ++ Tm.prettyString tm
       dotLabel vid (VTerm, Just tm) = show vid ++ " TERM: " ++ Tm.prettyString tm

       dotLabel vid _ = show vid

       edgeColor tp = case tp of
         Info.InitConstr _ -> "black"
         Info.DerivedEqn _ -> "red"
         Info.ChoiceEdge LeftChoice _ _ -> "blue"
         Info.ChoiceEdge RightChoice _ _ -> "cyan"

         _ -> "green"

       edgeName tp =
         case tp of
             Info.InitConstr pid -> show $ Info.probIdToName pid
             Info.DerivedEqn pid ->  "(" ++ (show $ Info.probIdToName pid)++ ")"
             Info.DefineMeta alpha -> "DEF " ++ show alpha
             Info.MetaUpdate (alpha, v) -> "MUPD " ++ show alpha ++ " := " ++ Tm.prettyString v
             _ -> ""

       dotEdges :: VertexId -> VertexInfo -> (String)
       --dotEdges _ _ = "" --TODO remove to show derived edges
       dotEdges vid (VertBot, _) = ""
       dotEdges vid (VVar,_) = ("")
       dotEdges vid ((VCon k),_) = ("")
      --  dotEdges vid ((VLam k1 k2),_) =
      --    (show vid ++ " -> " ++ show k1 ++ " [style = dashed, label = \"L\"];//1\n"
      --      ++ show vid ++ " -> " ++ show k2 ++ " [style = dashed, label = \"R\"];//2\n")
       dotEdges vid ((VApp k1 k2),_) =
         (show vid ++ " -> " ++ show k1  ++ " [style = dashed, label = \"L\"];//3\n"
           ++ show vid ++ " -> " ++ show k2 ++ " [style = dashed, label = \"R\"];//4\n")
      --  dotEdges vid ((VElim k1 k2),_) =
      --    (show vid ++ " -> " ++ show k1 ++ " [style = dashed, label = \"L\"];//5\n"
      --      ++ show vid ++ " -> " ++ show k2 ++ " [style = dashed, label = \"R\"];//6\n")
       dotEdges vid _ = ""

       termEdges = map (uncurry dotEdges) nodePairs

       nodeDecls =
        [show v ++ " [label = \"" ++ show v ++ ": " ++ dotLabel v vinfo ++ "\" ];\n" | (v, vinfo) <- nodePairs ]
        --[show num ++ " [label = \"" ++ s ++ "\" ];\n" | s <- termNames ]
       creator info = creationInfo $ edgeEqnInfo info
       edgeDecls =
          [show n1
          ++ " -> " ++ show n2
          ++ " [dir=none, label = \""
          ++ edgeName edgeType ++ " " ++ show (creator info)
          ++ "\", color = " ++ edgeColor edgeType ++ "] ;\n" | (n1, n2, info) <- theEdges, edgeType <- [Info.edgeType info]  ]


     in "digraph G\n{\n" ++ concat (nodeDecls) ++ concat (edgeDecls ++ termEdges) ++ "\n}"

addUpdateEdge vid info oldVal newVal g = do
  (newVid, g1) <- addTermGraph M.empty (Ln.s2n "theNode") newVal g
  addNewEdge (newVid, vid) (info (oldVal, newVal)) g1


processUpdate :: (Ln.Fresh m) => ((Tm.VAL, Tm.VAL) -> Info) -> (Tm.Nom, Tm.VAL) -> StandardTypeGraph -> m StandardTypeGraph
processUpdate info (alpha, alphaVal) stg = do
  let
    vertsToUpdate =
      [ (termVid, oldTerm, Ln.subst alpha alphaVal oldTerm) |
        Just termList <- [M.lookup alpha (termNodes stg)],
        (termVid, oldTerm) <- termList]
    foldFun :: (Ln.Fresh m) => (VertexId, Tm.VAL, Tm.VAL) -> StandardTypeGraph -> m StandardTypeGraph
    foldFun (vid, oldVal, newVal) g =
      addUpdateEdge vid info oldVal newVal g
  gRet <- foldrM foldFun stg vertsToUpdate
  --Mark the updates on these terms as performed
  let newDict = M.filterWithKey (\beta _ -> alpha /= beta) (termNodes gRet)
  return $ gRet {termNodes = newDict,
    collectedUpdates = M.insert alpha (alphaVal, info) (collectedUpdates gRet)}


-- Helper functions
combineClasses :: [VertexId] -> StandardTypeGraph -> StandardTypeGraph
combineClasses is stg =
      case nub (map (`representativeInGroupOf` stg) is) of
         list@(i:_:_) ->
            let eqgroups = map (`getGroupOf` stg) list
                newGroup = foldr combineGroups emptyGroup eqgroups
            in addPossibleInconsistentGroup i . createGroup newGroup . foldr removeGroup stg $ eqgroups
         _ -> stg

propagateEquality :: VertexId -> StandardTypeGraph -> StandardTypeGraph
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

addClique :: Clique -> StandardTypeGraph -> StandardTypeGraph
addClique clique =
   updateGroupOf (cliqueRepresentative clique) (insertClique clique) . combineClasses (childrenInClique clique)

propagateRemoval :: VertexId -> StandardTypeGraph -> StandardTypeGraph
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

--TODO abstract out parent edges fn


initialCreator :: StandardTypeGraph -> (EdgeId, Info) -> Maybe (EdgeId, Info)
initialCreator stg (edge, info) =
  let
    edgePairs = allEdges stg
    helper (thisEdge,ourInfo) lastEdge =
      case (creationInfo $ edgeEqnInfo ourInfo) of
        Info.Initial -> lastEdge
        Info.CreatedBy creator ->
          let
            parentEdges =
                [(eid, someInfo)
                  | (eid, someInfo) <- edgePairs
                  , Just potentialCreatorId <- [Info.constraintPid someInfo]
                  , creator == potentialCreatorId ]
            parentEdge = case parentEdges of
               [] -> error "No parent for "
               [x] -> x
               _ -> error "Too many parents"
          in
            helper parentEdge $ Just parentEdge
  in
    helper (edge,info) Nothing

removeDerived :: EdgeId -> StandardTypeGraph -> StandardTypeGraph
removeDerived e stg =
  let
    edgePairs = allEdges stg
    mEdgesToRemove = do
      let ourInfoList = [info | (someEdge, info) <- edgePairs, someEdge == e]
      ourInfo <- case ourInfoList of
        [ourInfo] -> return ourInfo
        _ -> Nothing
      ourPid <-
        Info.constraintPid ourInfo
      let childEdges = [eid | (eid, someInfo) <- edgePairs, (Info.creationInfo . Info.edgeEqnInfo) someInfo == Info.CreatedBy ourPid ]
      let
        mCreator =
          case (creationInfo $ edgeEqnInfo ourInfo) of
            Info.Initial -> Nothing
            Info.CreatedBy pid -> Just pid
      --When we diagnose a non-parent ID, we also remove its parent
      let parentEdges =
            [eid
              | Just creator <- [mCreator]
              , (eid, someInfo) <- edgePairs
              , Just potentialCreatorId <- [Info.constraintPid someInfo]
              , creator == potentialCreatorId ]
      return $ childEdges ++ parentEdges

  in
    case mEdgesToRemove of
      Nothing -> stg
      Just edgesToRemove -> foldr deleteEdge stg edgesToRemove


splitClass ::  VertexId -> StandardTypeGraph -> ([VertexId], StandardTypeGraph)
splitClass vid stg =
   let eqgroup   = getGroupOf vid stg
       newGroups = splitGroup eqgroup
       results   = [ vid2 | (vid2, _):_ <- map vertices newGroups ]
       newGraph
          | length newGroups > 1 = foldr createGroup (removeGroup eqgroup stg) newGroups
          | otherwise = stg
   in (results, newGraph)

deleteClique :: Clique -> StandardTypeGraph -> StandardTypeGraph
deleteClique clique =
   updateGroupOf (cliqueRepresentative clique) (removeClique clique)

-----------------------------------------------------------------

createGroup :: EquivalenceGroup Info -> StandardTypeGraph -> StandardTypeGraph
createGroup eqgroup stg =
   let newGroupNumber = equivalenceGroupCounter stg
       list = [(i, newGroupNumber) | (i, _) <- vertices eqgroup ]
   in if null list
        then internalError "Top.TypeGraph.TypeGraphMonad" "createNewGroup" "cannot create an empty equivalence group"
        else stg { referenceMap            = referenceMap stg `M.union` M.fromList list
                 , equivalenceGroupMap     = M.insert newGroupNumber eqgroup (equivalenceGroupMap stg)
                 , equivalenceGroupCounter = newGroupNumber + 1
                 }

removeGroup :: EquivalenceGroup Info -> StandardTypeGraph -> StandardTypeGraph
removeGroup eqgroup stg =
   let vertexIds   = map fst (vertices eqgroup)
       oldGroupNr  = maybeToList (M.lookup (head vertexIds) (referenceMap stg))
   in stg { referenceMap        = foldr M.delete (referenceMap stg) vertexIds
          , equivalenceGroupMap = foldr M.delete (equivalenceGroupMap stg) oldGroupNr
          }

updateGroupOf :: VertexId -> (EquivalenceGroup Info -> EquivalenceGroup Info) -> StandardTypeGraph -> StandardTypeGraph
updateGroupOf vid f stg =
   let eqgrp = getGroupOf vid stg
       err  = internalError "Top.TypeGraph.TypeGraphMonad" "updateEquivalenceGroupOf" ("error in lookup map: "++show vid)
       eqnr = M.findWithDefault err vid (referenceMap stg)
   in stg { equivalenceGroupMap = M.insert eqnr (f eqgrp) (equivalenceGroupMap stg) }

maybeGetGroupOf :: VertexId -> StandardTypeGraph -> Maybe (EquivalenceGroup Info)
maybeGetGroupOf vid stg =
   do eqnr <- M.lookup vid (referenceMap stg)
      let err = internalError "Top.TypeGraph.TypeGraphMonad" "equivalenceGroupOf" "error in lookup map"
      return (M.findWithDefault err eqnr (equivalenceGroupMap stg))

getGroupOf :: VertexId -> StandardTypeGraph -> EquivalenceGroup Info
getGroupOf vid =
   let err = internalError "Top.TypeGraph.Standard" "getGroupOf" ("the function getGroupOf does no longer create an empty group if the vertexId " ++ show vid ++ " doesn't exist")
   in fromMaybe err . maybeGetGroupOf vid

getAllGroups :: StandardTypeGraph -> [EquivalenceGroup Info]
getAllGroups = M.elems . equivalenceGroupMap

vertexExists :: VertexId -> StandardTypeGraph -> Bool
vertexExists vid = isJust . M.lookup vid . referenceMap

-----------------------------------------------------------------------------------

getPossibleInconsistentGroups :: StandardTypeGraph -> [VertexId]
getPossibleInconsistentGroups = possibleErrors

setPossibleInconsistentGroups :: [VertexId] -> StandardTypeGraph -> StandardTypeGraph
setPossibleInconsistentGroups vids stg = stg { possibleErrors = vids }

addPossibleInconsistentGroup :: VertexId -> StandardTypeGraph -> StandardTypeGraph
addPossibleInconsistentGroup vid stg = stg { possibleErrors = vid : possibleErrors stg }




-- addTermGraphM :: (Ln.Fresh m) => Tm.Subs -> Tm.Nom -> Tm.VAL -> StandardTypeGraph -> m (Tm.Nom, VertexId, StandardTypeGraph)
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
setHeuristics :: [Heuristic info] -> StandardTypeGraph -> StandardTypeGraph
setHeuristics = setPathHeuristics . const

setPathHeuristics :: (Path (EdgeId, info) -> [Heuristic info]) -> StandardTypeGraph -> StandardTypeGraph
setPathHeuristics f stg = stg {typegraphHeuristics = f}

getPathHeuristics :: StandardTypeGraph -> Path (EdgeId, info) -> [Heuristic info]
getPathHeuristics = typegraphHeuristics -}

typesInGroupOf :: VertexId -> StandardTypeGraph -> [Tm.VAL]
typesInGroupOf v stg = typesOfGroup M.empty $ getGroupOf v stg


addEqn
  :: (Ln.Fresh m)
  => Info -> (Tm.VAL, Tm.VAL)
  -> StandardTypeGraph
  -> m (StandardTypeGraph)
addEqn info (v1, v2) stg = do
    (var1, g1) <-  addTermGraph M.empty (Ln.s2n "theNode") v1 stg
    (var2, g2) <-  addTermGraph M.empty (Ln.s2n "theNode") v2 g1
    --edgeNr <- Ln.fresh $ Ln.s2n "edge"
    --let ourEdge = EdgeId var1 var2 $ EdgeNrX edgeNr
    addNewEdge (var1, var2) info g2
