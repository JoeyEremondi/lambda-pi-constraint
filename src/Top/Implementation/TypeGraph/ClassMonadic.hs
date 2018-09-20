{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Top.Implementation.TypeGraph.ClassMonadic where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified PatternUnify.Tm as Tm
import Top.Implementation.TypeGraph.Basics
import qualified Top.Implementation.TypeGraph.Class as TG
import Top.Interface.Basic
import Top.Interface.Qualification
import Top.Interface.TypeInference
import Top.Solver
import qualified Unbound.Generics.LocallyNameless as Ln

import Control.Monad.State.Lazy (runStateT, get, put)

class (HasBasic m info, {-HasTI m info, HasQual m info,-} HasTG m info, MonadWriter LogEntries m, Show info) => HasTypeGraph m info | m -> info

instance (HasBasic m info, {-HasTI m info, HasQual m info,-} HasTG m info, MonadWriter LogEntries m, Show info) => HasTypeGraph m info

class Monad m => HasTG m info | m -> info where
   withTypeGraph :: (forall graph . TG.TypeGraph graph info => graph -> (a, graph)) -> m a
   withTypeGraph f = withTypeGraphM (return . f)
   withTypeGraphM :: (forall graph . TG.TypeGraph graph info => graph -> m (a, graph)) -> m a

currentCounter :: (Monad m) => Ln.FreshMT m Integer
currentCounter = Ln.FreshMT get

setCounter :: (Monad m) => Integer -> Ln.FreshMT m ()
setCounter i = Ln.FreshMT $ put i

instance HasTG m info => HasTG (Ln.FreshMT m) info where
      withTypeGraphM f = do
            i <- currentCounter
            -- let f0 :: (forall graph . TG.TypeGraph graph info => graph -> m ((a, Integer), graph))
            let f0 g = do
                  ((a,g),ctr) <- (flip Ln.contFreshMT) i $ do
                        ret <- f g
                        ctr <- currentCounter
                        return (ret, ctr)
                  return ((a,ctr), g)
            (a,ctr) <- lift $ withTypeGraphM f0
            setCounter ctr
            return a


useTypeGraph :: HasTG m info => (forall graph . TG.TypeGraph graph info => graph -> a) -> m a
useTypeGraph f = withTypeGraph (\g -> (f g, g))

changeTypeGraph :: HasTG m info => (forall graph . TG.TypeGraph graph info => graph -> graph ) -> m ()
changeTypeGraph f = withTypeGraph (\g -> ((), f g))

changeTypeGraphM :: HasTG m info => (forall graph . TG.TypeGraph graph info => graph -> m graph ) -> m ()
changeTypeGraphM f = withTypeGraphM (\g -> (\fg -> ((), fg)) <$> f g)

--Perform some actions with a type graph, then return the
--graph to its original state
freezeTypeGraphM :: forall a m info. HasTG m info => m a -> m a
freezeTypeGraphM f = 
      let 
            theFn :: (forall graph . TG.TypeGraph graph info => graph -> m (a, graph))
            theFn g = do
                  ret <- f
                  return (ret, g)
      in withTypeGraphM theFn

-- construct a type graph

addTermGraph :: (HasTypeGraph m info, Ln.Fresh m) => Tm.VAL -> m VertexId
addTermGraph tp =
   do unique <- Ln.fresh $ Ln.s2n "addTermGraph"
      --synonyms <- getTypeSynonyms
      (vid) <- withTypeGraph
         $ \graph -> Ln.runFreshM $ TG.addTermGraph M.empty (Ln.s2n "addTerm") tp graph

      --setUnique newUnique
      return vid

addVertex :: HasTypeGraph m info => VertexId -> VertexInfo -> m ()
addVertex vid info = changeTypeGraph (TG.addVertex vid info)

addEdge :: HasTypeGraph m info => EdgeId -> info -> m ()
addEdge edgeId info = changeTypeGraph (TG.addEdge edgeId info)

addNewEdge :: HasTypeGraph m info => (VertexId, VertexId) -> info -> m ()
addNewEdge pair info = do
  changeTypeGraph (\gr -> Ln.runFreshM $ TG.addNewEdge pair info gr)

-- deconstruct a type graph

deleteEdge :: HasTypeGraph m info => EdgeId -> m ()
deleteEdge edgeId = changeTypeGraph (TG.deleteEdge edgeId)

-- inspect an equivalence group in a type graph

verticesInGroupOf :: HasTypeGraph m info => VertexId -> m [(VertexId, VertexInfo)]
verticesInGroupOf vid = useTypeGraph (TG.verticesInGroupOf vid)

childrenInGroupOf :: HasTypeGraph m info => VertexId -> m ([ParentChild], [ParentChild])
childrenInGroupOf vid = useTypeGraph (TG.childrenInGroupOf vid)

constantsInGroupOf :: HasTypeGraph m info => VertexId -> m [Constant]
constantsInGroupOf vid = useTypeGraph (TG.constantsInGroupOf vid)

representativeInGroupOf :: HasTypeGraph m info => VertexId -> m VertexId
representativeInGroupOf vid = useTypeGraph (TG.representativeInGroupOf vid)

edgesFrom :: HasTypeGraph m info => VertexId -> m [(EdgeId, info)]
edgesFrom vid = useTypeGraph (TG.edgesFrom vid)

allEdges :: HasTypeGraph m info =>  m [(EdgeId, info)]
allEdges = useTypeGraph TG.allEdges

getEdgeCreator :: HasTypeGraph m info =>  (EdgeId, info) -> m (Maybe (EdgeId, info))
getEdgeCreator e = useTypeGraph (TG.getEdgeCreator e)

-- query a path in an equivalence group
allPaths :: HasTypeGraph m info => VertexId -> VertexId -> m (TypeGraphPath info)
allPaths v1 v2 = useTypeGraph (TG.allPaths v1 v2)

allPathsList :: HasTypeGraph m info => VertexId -> [VertexId] -> m (TypeGraphPath info)
allPathsList v1 vs = useTypeGraph (TG.allPathsList v1 vs)

allPathsListWithout :: HasTypeGraph m info => S.Set VertexId -> VertexId -> [VertexId] -> m (TypeGraphPath info)
allPathsListWithout set v1 vs = useTypeGraph (TG.allPathsListWithout set v1 vs)

-- substitution and term graph
substituteVariable :: HasTypeGraph m info => Tm.Nom -> m Tm.VAL
substituteVariable i =
   do synonyms <- return M.empty
      useTypeGraph (TG.substituteVariable synonyms i)

substituteType :: HasTypeGraph m info => Tm.VAL -> m Tm.VAL
substituteType tp =
   do synonyms <- return M.empty
      useTypeGraph (TG.substituteType synonyms tp)

substituteTypeSafe :: HasTypeGraph m info => Tm.VAL -> m (Maybe Tm.VAL)
substituteTypeSafe tp =
   do synonyms <- return M.empty
      useTypeGraph (TG.substituteTypeSafe synonyms tp)

makeSubstitution   :: HasTypeGraph m info => m [(VertexId, Tm.VAL)]
makeSubstitution =
   do synonyms <- return M.empty
      useTypeGraph (TG.makeSubstitution synonyms)

typeFromTermGraph :: HasTypeGraph m info => VertexId -> m Tm.VAL
typeFromTermGraph vid = useTypeGraph (TG.typeFromTermGraph vid)

-- Extra administration
markAsPossibleError :: HasTypeGraph m info => VertexId -> m ()
markAsPossibleError vid = changeTypeGraph (TG.markAsPossibleError vid)

getMarkedPossibleErrors :: HasTypeGraph m info => m [VertexId]
getMarkedPossibleErrors = useTypeGraph TG.getMarkedPossibleErrors

unmarkPossibleErrors :: HasTypeGraph m info => m ()
unmarkPossibleErrors = changeTypeGraph TG.unmarkPossibleErrors

---------------------
------ EXTRA

theUnifyTerms :: (Ln.Fresh m, HasTypeGraph m info) => info -> Tm.VAL -> Tm.VAL -> m ()
theUnifyTerms info t1 t2 =
   do v1  <- addTermGraph t1
      v2  <- addTermGraph t2
      addNewEdge (v1, v2) info


makeFixpointSubst = error "TODO fixpointSubst"

getDot :: HasTypeGraph m info =>  m String
getDot = useTypeGraph $ TG.toDot

recordVar :: HasTypeGraph m info => Tm.Nom -> Tm.Param ->  m ()
recordVar n p = changeTypeGraph $ TG.recordVar n p

-- makeFixpointSubst :: HasTypeGraph m info => m FixpointSubstitution
-- makeFixpointSubst =
--    do xs <- makeSubstitution
--       let list = [ (i, tp) | (VertexId i, tp) <- xs ]
--       return (FixpointSubstitution (M.fromList list))
