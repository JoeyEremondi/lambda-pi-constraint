module PatternUnify.TypeGraphStuff where


import PatternUnify.Context

import qualified Top.Implementation.TypeGraph.Standard as TG
import qualified Top.Implementation.TypeGraph.ClassMonadic as CM
import qualified Top.Implementation.TypeGraph.ApplyHeuristics as Heur

instance CM.HasTG Contextual ConstraintInfo where
  withTypeGraphM f = do
    ourGraph <- getGraph
    (ret, newGraph) <- f ourGraph
    setGraph newGraph
    return ret
