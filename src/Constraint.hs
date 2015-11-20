module Constraint
{-
  ( ConType
  , ConTyFn
  , ConstraintM
  , Unifyable, unify, fresh
  , unknownIdent
  , evaluate
  , conType, conTyFn, liftConTyFn, valToFn
  , mkPi, applyPi, applyVal
  , mkNat, mkVec, mkEq
  ) -} where

import qualified Common
import Control.Monad.State
import qualified Control.Monad.Trans.UnionFind as UF
import Control.Monad.Writer
import Control.Monad.Trans
import Data.Data
import Data.Typeable


--We index type variables as unique integers
newtype TypeVar = TypeVar {getUF :: UF.Point TypeRepr}


data TypeRepr =
   BlankSlate
   | TypeRepr ConType


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

--A generic, top-down monadic traversal for our ConType class
--Apply a transformation bottom-up
--Does NOT traverse into ConTyFns --TODO is this right?
traverseConTypeM :: (Monad m) => (ConType -> m ConType) -> ConType -> m ConType
traverseConTypeM f t = f =<< (traverse' t)
  where
    self = traverseConTypeM f
    traverse' (PiType t1 tf) = PiType <$> self t1 <*> return tf
    traverse' (AppType tf t1) = AppType <$> return tf <*> self t1
    traverse' (NatType t) = NatType <$> self t
    traverse' (VecType t1 t2) = VecType <$> self t1 <*> self t2
    traverse' (EqType t1 t2 t3) = EqType <$> self t1 <*> self t2 <*> self t3
    traverse' x = return x


class Unifyable a where
  unify :: a -> a -> ConstraintM ()
  fresh :: ConstraintM a


  --Define a "Constrain" monad, which lets us generate
  --new variables and store constraints in our state


{-data ConstraintState =
  ConstraintState
  { pointSupply :: UF.PointSupply TypeRepr
  , constraintsSoFar :: [Constraint]
  }-}


type ConstraintM a = UF.UnionFindT TypeRepr (Writer [Constraint]) a

--Operations in our monad:
--Make fresh types, and unify types together
freshVar :: ConstraintM TypeVar
freshVar = do
  newPoint <- UF.fresh BlankSlate
  return $  TypeVar newPoint


instance Unifyable ConType where
  unify t1 t2 = addConstr (ConstrUnify t1 t2)
  fresh = VarType `fmap` freshVar

instance Unifyable ConTyFn where
  unify t1 t2 = addConstr (TyFnUnify t1 t2)
  fresh = TyFnVar `fmap` freshVar

evaluate :: Common.Value_ -> ConstraintM ConType
evaluate v = do
  t <- fresh
  addConstr $ ConstrEvaluatesTo t v
  return t

vappIs :: (ConType, ConType) -> ConType -> ConstraintM ()
vappIs (t1, t2) tresult =
  addConstr $ ConstrVapp (t1, t2) tresult

unknownIdent :: String -> ConstraintM a
unknownIdent = error --TODO: something smarter here

mkPi :: ConType -> ConTyFn -> ConType
mkPi = PiType

applyPi :: ConTyFn -> ConType -> ConType
applyPi = AppType

applyVal :: ConType -> ConType -> ConType
applyVal f x = (valToFn f) `applyPi` x

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

valToFn :: ConType -> ConTyFn
valToFn fcon = TyFn (\v -> AppType ( conTyFn $ \f -> conType $ f `Common.vapp_` v) fcon )


--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = lift $ tell [c]
