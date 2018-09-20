{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Top.Implementation.TypeGraph.Class where

import Data.List (nub)
import Data.Maybe
import qualified Data.Set as S
import Top.Implementation.TypeGraph.Basics
--import Top.Types
import Utils (internalError)

import qualified PatternUnify.Tm as Tm
import qualified Unbound.Generics.LocallyNameless as Ln

class TypeGraph graph info | graph -> info where

   -- construct a type graph
   addTermGraph :: (Ln.Fresh m) => Tm.Subs -> Tm.Nom -> Tm.VAL -> graph -> m (VertexId, graph)
   addVertex    :: VertexId -> VertexInfo -> graph -> graph
   addEdge      :: EdgeId -> info -> graph -> graph
   addNewEdge   :: (Ln.Fresh m) => (VertexId, VertexId) -> info -> graph -> m graph

   -- deconstruct a type graph
   deleteEdge :: EdgeId -> graph -> graph

   choiceInfo :: graph -> info

   -- inspect an equivalence group in a type graph
   verticesInGroupOf       :: VertexId -> graph -> [(VertexId, VertexInfo)]
   childrenInGroupOf       :: VertexId -> graph -> ([ParentChild], [ParentChild])
   constantsInGroupOf      :: VertexId -> graph -> [Constant]
   representativeInGroupOf :: VertexId -> graph -> VertexId
   edgesFrom               :: VertexId -> graph -> [(EdgeId, info)]
   isChildOf               :: VertexId -> VertexId -> graph -> Bool

   -- query a path in an equivalence group
   allPaths            :: VertexId -> VertexId -> graph -> TypeGraphPath info
   allPathsList        :: VertexId -> [VertexId] -> graph -> TypeGraphPath info
   allPathsListWithout :: S.Set VertexId -> VertexId -> [VertexId] -> graph -> TypeGraphPath info

   allEdges :: graph -> [(EdgeId, info)]

   -- substitution and term graph
   substituteVariable :: Tm.Subs -> Tm.Nom -> graph -> Tm.VAL
   substituteType     :: Tm.Subs -> Tm.VAL  -> graph -> Tm.VAL
   substituteTypeSafe :: Tm.Subs -> Tm.VAL  -> graph -> Maybe Tm.VAL
   makeSubstitution   :: Tm.Subs -> graph -> [(VertexId, Tm.VAL)]
   typeFromTermGraph  :: VertexId -> graph -> Tm.VAL

   -- Extra administration
   markAsPossibleError     :: VertexId -> graph -> graph
   getMarkedPossibleErrors :: graph -> [VertexId]
   unmarkPossibleErrors    :: graph -> graph

   getEdgeCreator ::  (EdgeId, info) -> graph -> Maybe (EdgeId, info)

   toDot :: graph -> String
   errorDot :: [EdgeId] -> graph -> String

   recordVar :: Tm.Nom -> Tm.Param -> graph -> graph
   getVarTypes :: graph -> [(Tm.Nom, Tm.Param)]

   -------------------------------------------
   -- default definitions

   allPaths i1 i2 =
      allPathsList i1 [i2]

   allPathsList =
      allPathsListWithout S.empty

   childrenInGroupOf i graph =
      unzip [ ( ParentChild { parent=p, child = t1, childSide=LeftChild  }
              , ParentChild { parent=p, child = t2, childSide=RightChild }
              )
            | (p, (VApp t1 t2, _)) <- verticesInGroupOf i graph
            ]

   constantsInGroupOf i graph =
      nub [ s | (_, (VCon s, _)) <- verticesInGroupOf i graph ]


   representativeInGroupOf i graph =
      case verticesInGroupOf i graph of
         (vid, _):_ -> vid
         _ -> internalError "Top.TypeGraph.TypeGraphState" "representativeInGroupOf" "unexpected empty equivalence group"

   substituteVariable syns =
      substituteType syns . Tm.var

   substituteType syns tp graph =
      let err = internalError "Top.TypeGraph.TypeGraphState" "substituteType" "inconsistent state"
      in fromMaybe err (substituteTypeSafe syns tp graph)

   -- Extra administration
   markAsPossibleError _     = id
   getMarkedPossibleErrors _ = []
   unmarkPossibleErrors      = id
