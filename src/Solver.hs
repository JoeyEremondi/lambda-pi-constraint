{-# LANGUAGE DeriveFunctor #-}
module Solver where

import Constraint
import Control.Monad.State
import qualified Data.Map as Map
import qualified Control.Monad.Trans.UnionFind as UF
import qualified Common
import Control.Applicative ((<$>), (<*>))



--Custom Error monad with a special option saying
--"Compotation failed, defer this unification"
data SolverResult a =
  Ok a
  | Defer
  | Err String
  deriving (Eq, Ord, Show, Functor)

instance Applicative SolverResult where
  pure = Ok
  fa <*> x =
    case fa of
      Defer -> Defer
      Err s -> Err s
      Ok f -> f <$> x

instance Monad SolverResult where
  a >>= f =
    case a of
      Defer -> Defer
      Err s -> Err s
      Ok a -> f a


type UnifyM a = UF.UnionFindT TypeRepr (StateT Int SolverResult ) a

freshInt :: UnifyM Int
freshInt = do
  i <- lift get
  lift $ put (i+1)
  return 1

unifyTypes :: ConType -> ConType -> UnifyM ConType
--unify two variables
unifyTypes (VarType t1) (VarType t2) = do
  r1 <- UF.descriptor $ getUF t1
  r2 <- UF.descriptor $ getUF t2
  --Union the identifiers
  UF.union (getUF t1) (getUF t2)
  case (r1, r2) of
    (BlankSlate, BlankSlate) ->
      return (VarType t2)
    pair -> do
      newRepr <-
        case pair of
          (BlankSlate, TypeRepr t2) ->
            return t2
          (TypeRepr t1, BlankSlate) ->
            return t1
          (TypeRepr t1, TypeRepr t2) ->
            unifyTypes t1 t2
      --Set the descriptor of our variable to be our newly computed unifier
      dummyPoint <- UF.fresh (TypeRepr newRepr)
      UF.union dummyPoint (getUF t1)
      return newRepr


--Unify a variable with something: look at its descriptor
--If it's blank, then set its descriptor to whatever we union with
--Otherwise, unify our descriptor with the whatever type we see
unifyTypes (VarType tvar) t2 = do
  r1 <- UF.descriptor $ getUF tvar
  case r1 of
    BlankSlate -> do
      dummyPoint <- UF.fresh (TypeRepr t2)
      UF.union (getUF tvar) dummyPoint
      return t2

    TypeRepr t1 ->
      unifyTypes t1 t2

--Same as above, but reversed --TODO just recurse?
unifyTypes t2 (VarType tvar) = do
  r1 <- UF.descriptor $ getUF tvar
  case r1 of
    BlankSlate -> do
      dummyPoint <- UF.fresh (TypeRepr t2)
      UF.union (getUF tvar) dummyPoint
      return t2
    TypeRepr t1 ->
      unifyTypes t1 t2

unifyTypes (LitType v1) (LitType v2) =
  error "TODO beta equality"

unifyTypes (PiType t1 f1) (PiType t2 f2) =
  PiType <$> unifyTypes t1 t2 <*> unifyFns f1 f2

--Application: try evaluating the application
unifyTypes (AppType f1 t1) t2 = do
  v1 <- toRealType t1
  fv1 <- toRealTyFn f1
  unifyTypes (LitType $ fv1 v1) t2

--Same as above, but flip args
unifyTypes t2 (AppType f1 t1) = do
  v1 <- toRealType t1
  fv1 <- toRealTyFn f1
  unifyTypes (LitType $ fv1 v1) t2

unifyTypes (NatType t1) (NatType t2) = do
  NatType <$> unifyTypes t1 t2

unifyTypes (VecType t1 n1) (VecType t2 n2) = do
  VecType <$> unifyTypes t1 t2 <*> unifyTypes n1 n2

unifyTypes (EqType t1 x1 y1) (EqType t2 x2 y2) = do
  EqType <$> unifyTypes t1 t2 <*> unifyTypes x1 x2 <*> unifyTypes y1 y2

unifyTypes _ _ = error "Unification failed!"

--Check if we can look at a ConType and replace all of its
--Type variables with their actual types, that we've resolved through unification
--If not, then we use a Defer error in our monad to delay this check until later
toRealType :: ConType -> UnifyM Common.Type_
toRealType (LitType t) = return t

toRealType (VarType v) = do
  repr <- UF.descriptor (getUF v)
  case repr of
    BlankSlate -> lift $ lift $ Defer
    TypeRepr x -> toRealType x

toRealType (PiType t f) = Common.VPi_ <$> toRealType t <*> toRealTyFn f

toRealTyFn :: ConTyFn -> UnifyM (Common.Type_ -> Common.Type_)
toRealTyFn (TyFn f) = mkFunctionReal f
toRealTyFn (TyFnVar v) = do
  repr <- UF.descriptor $ getUF v
  case repr of
    BlankSlate -> lift $ lift $ Defer
    TypeFnRepr f -> mkFunctionReal f

--Replace every type variable with its descriptor
replaceTypeVars :: ConType -> UnifyM ConType
replaceTypeVars = traverseConTypeM replace
  where
    replace t@(VarType v) = do
      repr <- UF.descriptor $ getUF v
      case repr of
        BlankSlate -> return t
        TypeRepr tr -> return tr


unifyFns = error "TODO"

betaEqual = error "TODO"

--A generic, bottom-up monadic traversal for our ConType class
--Apply a transformation bottom-up
--Does NOT traverse into ConTyFns --TODO is this right?
traverseConTypeM
  :: (ConType -> UnifyM ConType)
  -> ConType
  -> UnifyM ConType
traverseConTypeM f t = do
  appliedToSub <- (traverse' t)
  f appliedToSub
  where
    self = traverseConTypeM f
    traverse' (PiType t1 tf) = PiType <$> self t1 <*> return tf
    traverse' (AppType tf t1) = AppType <$> return tf <*> self t1
    traverse' (NatType t) = NatType <$> self t
    traverse' (VecType t1 t2) = VecType <$> self t1 <*> self t2
    traverse' (EqType t1 t2 t3) = EqType <$> self t1 <*> self t2 <*> self t3
    traverse' x = return x

--TODO do we want a Value or a Term as a result of this?
mkFunctionReal :: (Common.Type_ -> ConType) -> UnifyM (Common.Type_ -> Common.Type_)
mkFunctionReal f = do
  freeVar <- (Common.vfree_ . Common.Quote) <$> freshInt
  let funBody = f freeVar
  --Turn our result from a ConType into a Type_, if we can
  valBody <- toRealType funBody
  --Abstract over the free variable
  return $ \v -> _subst freeVar v valBody
