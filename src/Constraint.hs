module Constraint
  ( ConType
  , ConstraintM
  , freshType
  , unify
  , unknownIdent
  , evaluatesTo
  , contype
  ) where

import qualified Common
import Control.Monad.State


--We index type variables as unique integers
newtype TypeVar = TypeVar {varIdent :: Int}


--Type we can unify over: either a type literal
--Or a type variable
data ConType =
  VarType TypeVar --Type variable can represent a type
  | LitType Common.Type_ --We look at literal types in our constraints
  | PiType ConType ConType --Sometimes we look at function types, where the types
                       --may be variables we resolve later with unification


--Initially, the only constraint we express is that two types unify
data Constraint =
  ConstrUnify ConType ConType
  | ConstrEvaluatesTo ConType Common.Value_


  --Define a "Constrain" monad, which lets us generate
  --new variables and store constraints in our state


data ConstraintState =
  ConstraintState
  { nextTypeVar :: Int
  , constraintsSoFar :: [Constraint]
  }


type ConstraintM a = State ConstraintState a

--Operations in our monad:
--Make fresh types, and unify types together
freshType :: ConstraintM ConType
freshType = do
  currentState <- get
  let nextInt = nextTypeVar currentState
  put $ currentState {nextTypeVar = nextInt + 1}
  return $ VarType $ TypeVar nextInt


unify :: ConType -> ConType -> ConstraintM ()
unify t1 t2 = addConstr (ConstrUnify t1 t2)


evaluatesTo :: ConType -> Common.Value_ -> ConstraintM ()
evaluatesTo t v = addConstr $ ConstrEvaluatesTo t v

unknownIdent :: String -> ConstraintM a
unknownIdent = error --TODO: something smarter here


contype = LitType

--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = do
  --Add the new constraint to our state
  oldState <- get
  let oldConstrs = constraintsSoFar oldState
  put $ oldState {constraintsSoFar = c : oldConstrs}
  return ()
