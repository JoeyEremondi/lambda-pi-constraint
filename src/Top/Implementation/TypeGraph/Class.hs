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

class TypeGraph graph info | graph -> info where

   -- construct a type graph
   addTermGraph :: Int -> Tm.VAL -> graph -> (Int, VertexId, graph)
   addVertex    :: VertexId -> VertexInfo -> graph -> graph
   addEdge      :: EdgeId -> info -> graph -> graph
   addNewEdge   :: (VertexId, VertexId) -> info -> graph -> graph

   -- deconstruct a type graph
   deleteEdge :: EdgeId -> graph -> graph

   -- inspect an equivalence group in a type graph
   verticesInGroupOf       :: VertexId -> graph -> [(VertexId, VertexInfo)]
   childrenInGroupOf       :: VertexId -> graph -> ([ParentChild], [ParentChild])
   constantsInGroupOf      :: VertexId -> graph -> [String]
   representativeInGroupOf :: VertexId -> graph -> VertexId
   edgesFrom               :: VertexId -> graph -> [(EdgeId, info)]

   -- query a path in an equivalence group
   allPaths            :: VertexId -> VertexId -> graph -> TypeGraphPath info
   allPathsList        :: VertexId -> [VertexId] -> graph -> TypeGraphPath info
   allPathsListWithout :: S.Set VertexId -> VertexId -> [VertexId] -> graph -> TypeGraphPath info

   -- substitution and term graph
   substituteVariable :: Int -> graph -> Tm.VAL
   substituteType     ::  Tm.VAL  -> graph -> Tm.VAL
   substituteTypeSafe :: Tm.VAL  -> graph -> Maybe Tm.VAL
   makeSubstitution   :: graph -> [(VertexId, Tm.VAL)]
   typeFromTermGraph  :: VertexId -> graph -> Tm.VAL

   -- Extra administration
   markAsPossibleError     :: VertexId -> graph -> graph
   getMarkedPossibleErrors :: graph -> [VertexId]
   unmarkPossibleErrors    :: graph -> graph

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

   substituteVariable syns = error "TODO substituteVariable"
      --substituteType syns . TVar

   substituteType tp graph =
      let err = internalError "Top.TypeGraph.TypeGraphState" "substituteType" "inconsistent state"
      in fromMaybe err (substituteTypeSafe tp graph)

   -- Extra administration
   markAsPossibleError _     = id
   getMarkedPossibleErrors _ = []
   unmarkPossibleErrors      = id
