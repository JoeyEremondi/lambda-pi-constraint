module Constraint
  ( ConType
  , ConTyFn
  , ConstraintM
  , Unifyable, unify, fresh
  , unknownIdent
  , evaluatesTo, vappIs
  , conType, conTyFn, liftConTyFn
  , mkPi, applyPi
  , mkNat, mkVec, mkEq
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
  | AppType ConTyFn ConType --Used to encode
                       --may be variables we resolve later with unification
  | NatType ConType --Our built-in data constructors
  | VecType ConType ConType
  | EqType ConType ConType ConType


--Wrapper for functions on types, whose values we may not know
--But instead determine from inference
data ConTyFn =
  TyFnVar TypeVar
  | TyFn (Common.Type_ -> ConType)

--Initially, the only constraint we express is that two types unify
data Constraint =
  ConstrUnify ConType ConType
  | TyFnUnify ConTyFn ConTyFn
  | ConstrEvaluatesTo ConType Common.Value_
  | ConstrVapp (ConType, ConType) ConType


class Unifyable a where
  unify :: a -> a -> ConstraintM ()
  fresh :: ConstraintM a


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
freshVar :: ConstraintM TypeVar
freshVar = do
  currentState <- get
  let nextInt = nextTypeVar currentState
  put $ currentState {nextTypeVar = nextInt + 1}
  return $  TypeVar nextInt


instance Unifyable ConType where
  unify t1 t2 = addConstr (ConstrUnify t1 t2)
  fresh = VarType `fmap` freshVar

instance Unifyable ConTyFn where
  unify t1 t2 = addConstr (TyFnUnify t1 t2)
  fresh = TyFnVar `fmap` freshVar

evaluatesTo :: ConType -> Common.Value_ -> ConstraintM ()
evaluatesTo t v = addConstr $ ConstrEvaluatesTo t v

vappIs :: (ConType, ConType) -> ConType -> ConstraintM ()
vappIs (t1, t2) tresult =
  addConstr $ ConstrVapp (t1, t2) tresult

unknownIdent :: String -> ConstraintM a
unknownIdent = error --TODO: something smarter here

mkPi :: ConType -> ConTyFn -> ConType
mkPi = PiType

applyPi :: ConTyFn -> ConType -> ConType
applyPi = AppType

mkNat :: ConType -> ConType
mkNat = NatType

mkVec :: ConType -> ConType -> ConType
mkVec = VecType

mkEq :: ConType -> ConType -> ConType -> ConType
mkEq = EqType


conType :: Common.Type_ -> ConType
conType = LitType

conTyFn :: (Common.Type_ -> ConType) -> ConTyFn
conTyFn = TyFn

liftConTyFn :: (Common.Type_ -> Common.Type_) -> ConTyFn
liftConTyFn f = TyFn ( conType . f )


--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = do
  --Add the new constraint to our state
  oldState <- get
  let oldConstrs = constraintsSoFar oldState
  put $ oldState {constraintsSoFar = c : oldConstrs}
  return ()
