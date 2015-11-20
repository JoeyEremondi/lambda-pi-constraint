module Solver where

import Constraint
import Control.Monad.State
import qualified Data.Map as Map


unify :: ConType -> ConType ->  ()
unify (VarType t1) (VarType t2) =
  _
