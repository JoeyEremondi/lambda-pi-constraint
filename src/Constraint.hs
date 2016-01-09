{-# LANGUAGE FlexibleInstances #-}
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
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Identity (Identity)
import Data.Data
import Data.Typeable

import PatternUnify.Tm as Tm

cToUnifForm :: Common.CTerm_ -> Tm.VAL
cToUnifForm (Common.L _ tm) =
  case tm of
    Common.Inf_ itm ->
      iToUnifForm itm
    Common.Lam_ ctm ->
      Tm.L ( (error "TODO bind") (cToUnifForm ctm) )
    _ ->
      error "TODO conversions for Vec, Eq, Nat"


iToUnifForm :: Common.ITerm_ -> Tm.VAL
iToUnifForm ltm@(Common.L _ tm) =
  case tm of
    Common.Ann_ val tp ->
      error "TODO annotated val"

    Common.Star_ ->
      Tm.SET

    Common.Pi_ s t ->
      Tm.PI (cToUnifForm s) (cToUnifForm t)

    Common.Bound_ i ->
      error "TODO bound variables to Solver form"

    Common.Free_ nm ->
      error "TODO neutral terms1"

    (_ Common.:$: _) ->
      let
        (startHead, startSpine) = appToSpine ltm
      in
        case startHead of
          Common.Bound i ->
            Tm.N (Tm.Var ((error "TODO deBruijn to name") i) Tm.Only) (map (Tm.A . cToUnifForm) startSpine)
          Common.Ann (Common.Lam fnBody) fnTy ->
            error "TODO reduce lambda redex for typechecking?"

    _ -> error "TODO builtIn types"

--TODO make tail recursive?
appToSpine :: Common.ITerm_ -> (Common.ITerm_, [Common.CTerm_])
--Application: look into function to find head
appToSpine (Common.App it ct) =
  let
    (subHead, subSpine) = appToSpine it
  in
    (subHead, subSpine ++ [ct])
--Other expression:
appToSpine e = (e, [])

type ConstrContext = [(Common.Name, ConType)]
type WholeEnv = (Common.NameEnv Common.Value_, ConstrContext)

--We index type variables as unique integers
newtype TypeVar = TypeVar (UF.Point TypeRepr, Int)

getUF (TypeVar x) = fst x

instance Show TypeVar where
  show (TypeVar (_, i)) = "<" ++ show i ++ ">"

data TypeRepr =
   BlankSlate
   | TypeRepr ConType
   | TypeFnRepr (Common.Type_ -> ConType)
   deriving (Show)


--Type we can unify over: either a type literal
--Or a type variable
data ConType =
  VarType TypeVar --Type variable can represent a type
  | LitType Common.Type_ --We look at literal types in our constraints
  | PiType ConType ConTyFn --Sometimes we look at function types, where the types
  | AppType ConTyFn ConType --Used to encode
                       --may be variables we resolve later with unification
  | NatType --Our built-in data constructors
  | VecType ConType ConType
  | EqType ConType ConType ConType
--  | Param (UF.Point TypeRepr) --Used as a placeholder to deal with functions
                  --The point is just used as a unique identifier
  deriving (Show)

instance Show (UF.Point a) where
  show _ = "var"

--Wrapper for functions on types, whose values we may not know
--But instead determine from inference
data ConTyFn =
  TyFnVar TypeVar
  | TyFn (Common.Type_ -> ConType)
  deriving (Show)

instance Show (Common.Type_ -> ConType) where
  show f = "(\\(-1) -> " ++ (show $ f $ Common.vfree_ (Common.Quote (0-1)) )++ ")"

--Initially, the only constraint we express is that two types unify
data Constraint =
  ConstrUnify ConType ConType WholeEnv
  | TyFnUnify ConTyFn ConTyFn WholeEnv
  | ConstrEvaluatesTo ConType Common.CTerm_ WholeEnv

maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (h:_) = Just h

instance Show Constraint where
  show (ConstrUnify t1 t2 env) = "\n" ++ (show t1) ++ " === " ++ (show t2) ++ " |ENV: " ++ show (maybeHead $ snd env)
  show (TyFnUnify t1 t2 env) = "\n" ++(show t1) ++ " === " ++ (show t2) ++ " |ENV: " ++ show ( maybeHead $ snd env)
  show (ConstrEvaluatesTo t term env) = "\n" ++(show t) ++ " ~~> " ++ (show term) ++ " |ENV: " ++ show ( maybeHead $ snd env)



class Unifyable a where
  unify :: a -> a -> WholeEnv -> ConstraintM ()
  fresh :: ConstraintM a


  --Define a "Constrain" monad, which lets us generate
  --new variables and store constraints in our state


{-data ConstraintState =
  ConstraintState
  { pointSupply :: UF.PointSupply TypeRepr
  , constraintsSoFar :: [Constraint]
  }-}


type UFM = UF.UnionFindT TypeRepr Identity

type ConstraintM a = WriterT [Constraint] (StateT [Int] UFM) a

--Operations in our monad:
--Make fresh types, and unify types together
freshVar :: ConstraintM TypeVar
freshVar = do
  newInt <- freshInt
  newPoint <- lift $ lift $ UF.fresh BlankSlate
  return $  TypeVar (newPoint, newInt)


freshInt :: ConstraintM Int
freshInt = do
  (h:t) <- lift $ get
  put t
  return h

instance Unifyable ConType where
  unify t1 t2 env = addConstr (ConstrUnify t1 t2 env)
  fresh = VarType <$> freshVar

instance Unifyable ConTyFn where
  unify t1 t2 env = addConstr (TyFnUnify t1 t2 env)
  fresh = TyFnVar <$> freshVar

evaluate :: Common.CTerm_ -> WholeEnv -> ConstraintM ConType
evaluate term env = do
  t <- fresh
  addConstr $ ConstrEvaluatesTo t term env
  return t


unknownIdent :: String -> ConstraintM a
unknownIdent s = error $ "Unknown Identifier: " ++ show s

mkPi :: ConType -> ConTyFn -> ConType
mkPi = PiType

applyPi :: ConTyFn -> ConType -> ConType
applyPi = AppType

applyVal :: ConType -> ConType -> ConType
applyVal f x = (valToFn f) `applyPi` x

mkNat :: ConType
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
valToFn fcon = error "ValToFn" $ TyFn (\v -> AppType ( conTyFn $ \f -> conType $ f `Common.vapp_` v) fcon )


--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = tell [c]
