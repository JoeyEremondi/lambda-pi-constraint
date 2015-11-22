{-# LANGUAGE DeriveFunctor #-}
module Solver where

import Constraint
import Control.Monad.State
import qualified Data.Map as Map
import qualified Control.Monad.Trans.UnionFind as UF
import qualified Common
import Control.Monad.Writer
import Control.Applicative ((<$>), (<*>))
import Control.Monad (forM)
import Control.Monad.Identity (runIdentity)

import Debug.Trace (trace)



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


newtype SolverResultT m a = SolverResultT {runSolverResultT :: m (SolverResult a)}
  deriving (Functor)

instance (Monad m) => Applicative (SolverResultT m) where
  pure = lift . return
  (SolverResultT mf) <*> (SolverResultT mx) = SolverResultT $ do
    f <- mf
    x <- mx
    return $ (f <*> x)

instance (Monad m) => Monad (SolverResultT m) where
  (SolverResultT mx) >>= f = SolverResultT $ do
    x <- mx
    case x of
      Ok a -> runSolverResultT $ f a
      Err s -> return $ Err s
      Defer -> return Defer



instance MonadTrans SolverResultT where
  lift x = SolverResultT (liftM Ok x)

type UnifyM a = SolverResultT (StateT [Int] UFM ) a

freshFreeIndex :: UnifyM Int
freshFreeIndex = do
  (h:t) <- lift $ get
  lift $ put t
  return h

getRepr :: TypeVar -> UnifyM TypeRepr
getRepr v = do
  repr <- lift $ lift $ UF.descriptor (getUF v)
  return $ trace ("\nRepr for " ++ show v ++ " is " ++ show repr) $ repr

unifyVars :: TypeVar -> TypeVar -> UnifyM ()
unifyVars v1 v2 = lift $ lift $ UF.union (getUF v1) (getUF v2)

setRepr :: TypeVar -> TypeRepr -> UnifyM ()
setRepr v rep = lift $ lift $ do
  dummyPoint <- UF.fresh rep
  UF.union (getUF v) dummyPoint

err :: String -> UnifyM a
err msg = SolverResultT $ return $ Err msg

defer :: UnifyM a
defer = SolverResultT $ return Defer


unifyTypes :: ConType -> ConType -> WholeEnv -> UnifyM ConType
--unify two variables
unifyTypes (VarType t1 i1) (VarType t2 i2) env = do
  r1 <- getRepr t1
  r2 <- getRepr t2
  --Union the identifiers
  unifyVars t1 t2
  case (r1, r2) of
    (BlankSlate, BlankSlate) ->
      return (VarType t2 i2)
    pair -> do
      newRepr <-
        case pair of
          (BlankSlate, TypeRepr t2) ->
            return t2
          (TypeRepr t1, BlankSlate) ->
            return t1
          (TypeRepr t1, TypeRepr t2) ->
            unifyTypes t1 t2 env
      --Set the descriptor of our variable to be our newly computed unifier
      setRepr t1 (TypeRepr newRepr)
      return newRepr


--Unify a variable with something: look at its descriptor
--If it's blank, then set its descriptor to whatever we union with
--Otherwise, unify our descriptor with the whatever type we see
unifyTypes (VarType tvar _) t2 env = do
  r1 <- getRepr tvar
  case r1 of
    BlankSlate -> do
      setRepr tvar (TypeRepr t2)
      return t2

    TypeRepr t1 ->
      unifyTypes t1 t2 env

--Same as above, but reversed --TODO just recurse?
unifyTypes t2 (VarType tvar _) env = do
  r1 <- getRepr tvar
  case r1 of
    BlankSlate -> do
      setRepr tvar (TypeRepr t2)
      return t2
    TypeRepr t1 ->
      unifyTypes t1 t2 env

unifyTypes (LitType v1) (LitType v2) env =
  case (Common.quote0_ v1) == (Common.quote0_ v2) of
    True -> return  $ LitType v1
    False -> err $ "The values " ++ show v1 ++ " and " ++ show v2 ++ " do not evaluate to the same normal form"

unifyTypes (PiType t1 f1) (PiType t2 f2) env =
  PiType <$> unifyTypes t1 t2 env <*> unifyFns f1 f2 env
--We can unify variable pi with literal pi
unifyTypes (PiType t1 f1) (LitType (Common.VPi_ treal freal)) env = do
  rep1 <- unifyTypes t1 (LitType treal) env
  rep2 <- unifyFns f1 (liftConTyFn freal) env
  return $ PiType rep1 rep2
--Same as above but reversed
unifyTypes (LitType (Common.VPi_ treal freal)) (PiType t1 f1) env  = do
  rep1 <- unifyTypes t1 (LitType treal) env
  rep2 <- unifyFns f1 (liftConTyFn freal)  env
  return $ PiType rep1 rep2

--Application: try evaluating the application
unifyTypes (AppType f1 t1) t2 env = do
  v1 <- toRealType t1 env
  fv1 <- toRealTyFn f1 env
  unifyTypes (LitType $ fv1 v1) t2 env

--Same as above, but flip args
unifyTypes t2 (AppType f1 t1)  env = do
  v1 <- toRealType t1 env
  fv1 <- toRealTyFn f1 env
  unifyTypes (LitType $ fv1 v1) t2 env

unifyTypes (NatType t1) (NatType t2) env = do
  NatType <$> unifyTypes t1 t2 env

unifyTypes (VecType t1 n1) (VecType t2 n2) env = do
  VecType <$> unifyTypes t1 t2 env <*> unifyTypes n1 n2 env

unifyTypes (EqType t1 x1 y1) (EqType t2 x2 y2) env = do
  EqType <$> unifyTypes t1 t2 env <*> unifyTypes x1 x2 env <*> unifyTypes y1 y2 env

unifyTypes t1 t2 _ = err $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

--Check if we can look at a ConType and replace all of its
--Type variables with their actual types, that we've resolved through unification
--If not, then we use a Defer error in our monad to delay this check until later
toRealType :: ConType -> WholeEnv -> UnifyM Common.Type_
toRealType (LitType t) _ = return t

toRealType (VarType v _) env = do
  repr <- getRepr v
  case repr of
    BlankSlate -> defer
    TypeRepr x -> toRealType x env

toRealType (PiType t f) env = Common.VPi_ <$> toRealType t env <*> toRealTyFn f env

toRealTyFn :: ConTyFn -> WholeEnv -> UnifyM (Common.Type_ -> Common.Type_)
toRealTyFn (TyFn f) env = mkFunctionReal f env
toRealTyFn (TyFnVar v _) env = do
  repr <- getRepr v
  case repr of
    BlankSlate -> defer
    TypeFnRepr f -> mkFunctionReal f env


--Unify functions:
--In theory, we're just keeping track of variables, and shouldn't
--Need to actually unify two functions
--TODO is this right?
unifyFns :: ConTyFn -> ConTyFn -> WholeEnv -> UnifyM ConTyFn
unifyFns (TyFnVar v1 i) (TyFnVar v2 _) env = do
  repr1 <- getRepr v1
  repr2 <- getRepr v2
  unifyVars v1 v2
  case (repr1, repr2) of
    (BlankSlate, BlankSlate) -> do
      --Descriptor doesn't matter in this case
      return (TyFnVar v1 i)
    (TypeFnRepr f1, BlankSlate) -> do
      --Take descriptor from first one
      setRepr v2 (TypeFnRepr f1)
      return $ TyFn f1
    (BlankSlate, TypeFnRepr f2) -> do
      --Take descriptor from second one
      setRepr v1 (TypeFnRepr f2)
      return $ TyFn f2

unifyFns (TyFnVar v1 i) (TyFn f2) env = do
  setRepr v1 $ TypeFnRepr f2
  return $ TyFn f2

--Same as above but with arguments flipped
unifyFns (TyFn f2) (TyFnVar v1 i) env = do
  setRepr v1 $ TypeFnRepr f2
  return $ TyFn f2

--TODO do we want a Value or a Term as a result of this?
mkFunctionReal :: (Common.Type_ -> ConType) -> WholeEnv -> UnifyM (Common.Type_ -> Common.Type_)
mkFunctionReal f env@(nameEnv, context) = do
  freeName <- Common.Quote <$> freshFreeIndex
  let freeVar = Common.vfree_ freeName
  let funBody = f freeVar
  --Turn our result from a ConType into a Type_, if we can
  valBody <- toRealType funBody env
  --Realize all the values in our environment
  realContext <- forM context (\(_, cval) -> toRealType cval env)
  --Quote that body back into a term
  let termBody = Common.quote0_ valBody
  --Abstract over the free variable
  return $ \v -> Common.cEval_ termBody ((freeName, v) : nameEnv, realContext)

solveConstraint :: Constraint -> UnifyM ()
solveConstraint (ConstrUnify t1 t2 env) =  unifyTypes t1 t2 env >>=  \_ -> return ()
solveConstraint (TyFnUnify f1 f2 env) = unifyFns f1 f2 env >>=  \_ -> return ()
solveConstraint (ConstrEvaluatesTo ct term env@(nameEnv, context)) = do
  realContext <- forM context $ \(_, cval) -> toRealType cval (nameEnv, [])
  let evaluated = Common.cEval_ term (nameEnv, realContext) --TODO need anything in env?
  unifyTypes ct (LitType evaluated) env >>=  \_ -> return () --TODO control eval?

--Loop through our constraints
solveConstraintList [] = return ()
solveConstraintList (c:rest) =  do
  result <- trace (show c) $ lift $ runSolverResultT $ solveConstraint c
  case result of
    --If defer: do this constraint later
    --TODO better solution for this?
    Defer -> trace "Deferring" $ solveConstraintList (rest ++ [c])
    Err s -> err s
    Ok _ -> solveConstraintList rest

solveConstraints :: (ConstraintM (ConType, TypeVar)) -> UnifyM Common.Type_
solveConstraints cm = do
  ( (mainType, mainTypeVar), constraintList) <- lift $ lift $  (\x -> evalStateT x [1..]) $ runWriterT cm
    --TODO what env for top constraint?
  solveConstraintList (ConstrUnify (VarType mainTypeVar 0) mainType ([],[]) : constraintList)
  (TypeRepr finalRepr) <- getRepr mainTypeVar
  toRealType finalRepr ([],[])


finalResults :: UnifyM Common.Type_ -> SolverResult Common.Type_
finalResults mcomp =
  let
    stateResult = runSolverResultT mcomp
    ufResult = evalStateT stateResult [1..]
    finalResult = runIdentity $ UF.runUnionFind ufResult
  in finalResult
