module Constraint
  ( ConType
  , ConstraintM
  , freshType
  , unify
  , unknownIdent
  , evaluatesTo
  , contype
  , mkPi
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
  | PiType ConType ConTyFn --Sometimes we look at function types, where the types
  | AppType ConType ConType --Used to encode
                       --may be variables we resolve later with unification


--Wrapper for functions on types, whose values we may not know
--But instead determine from inference
data ConTyFn =
  TyFnVar TypeVar
  | TyFn (Common.Type -> Common.Type)

--Initially, the only constraint we express is that two types unify
data Constraint =
  ConstrUnify ConType ConType
  | TyFnUnify ConTyFn ConTyFn
  | ConstrEvaluatesTo ConType Common.Value_


class Unifyable a where
  unify :: a -> a -> ConstraintM ()


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


instance Unifyable ConType where
  unify t1 t2 = addConstr (ConstrUnify t1 t2)

instance Unifyable ConTyFn where
  unify t1 t2 = addConstr (TyFnUnify t1 t2)

evaluatesTo :: ConType -> Common.Value_ -> ConstraintM ()
evaluatesTo t v = addConstr $ ConstrEvaluatesTo t v

unknownIdent :: String -> ConstraintM a
unknownIdent = error --TODO: something smarter here

mkPi :: ConType -> ConType -> ConType
mkPi = error "TODO"


contype = LitType

--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = do
  --Add the new constraint to our state
  oldState <- get
  let oldConstrs = constraintsSoFar oldState
  put $ oldState {constraintsSoFar = c : oldConstrs}
  return ()
