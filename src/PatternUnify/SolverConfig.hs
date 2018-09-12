module PatternUnify.SolverConfig where

data SolverConfig =
  SolverConfig
  { useCF        :: Bool
  , useTypeGraph :: Bool
  , useDot       :: Bool
  }
