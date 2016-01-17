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
import qualified Control.Monad.Trans.UnionFind as UF
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Identity (Identity)
import Data.Data
import Data.Typeable

import qualified Unbound.LocallyNameless as LN

import PatternUnify.Tm as Tm

import qualified PatternUnify.Context as UC

{-
cToUnifForm0 = cToUnifForm 0

cToUnifForm :: Int -> Common.CTerm_ -> Tm.VAL
cToUnifForm ii (Common.L _ tm) =
  case tm of
    Common.Inf_ itm -> --Here we bind a new variable, so increase our counter
      iToUnifForm ii itm
    Common.Lam_ ctm ->
      let
        newNom = deBrToNom ii 0
        retBody = cToUnifForm (ii + 1) ctm
      in
        Tm.L $ LN.bind newNom retBody
    _ ->
      error "TODO conversions for Vec, Eq, Nat"

deBrToNom :: Int -> Int -> Tm.Nom
deBrToNom ii i = LN.integer2Name $ toInteger $ ii - i

iToUnifForm :: Int -> Common.ITerm_ -> Tm.VAL
iToUnifForm ii ltm@(Common.L _ tm) =
  case tm of
    Common.Ann_ val tp ->
      error "TODO annotated val"

    Common.Star_ ->
      Tm.SET

    Common.Pi_ s t ->
      Tm.PI (cToUnifForm ii s) (cToUnifForm ii t)

    Common.Bound_ i ->
      var $ deBrToNom ii i --Take our current depth, minus deBruijn index --TODO check

    --If we reach this point, then our neutral term isn't embedded in an application
    Common.Free_ fv ->
      case fv of
        Common.Global nm ->
          Tm.vv nm
        Common.Local i ->
          var $ LN.integer2Name $ toInteger $ ii - i --Take our current depth, minus deBruijn index
        Common.Quote i ->
          error "Shouldn't come across quoted during checking"

    (_ Common.:$: _) ->
      let
        (startHead, startSpine) = appToSpine ltm
        convertedSpine = (map (Tm.A . (cToUnifForm ii)) startSpine)
      in
        case startHead of
          Common.Bound i ->
            Tm.N (Tm.Var (deBrToNom ii i) Tm.Only) convertedSpine
          Common.Free (Common.Global nm) ->
            Tm.N (Tm.Var (LN.s2n nm) Tm.Only ) convertedSpine
          Common.Ann (Common.Lam fnBody) fnTy ->
            error "TODO reduce lambda redex for typechecking?"

    _ -> error "TODO builtIn types"
-}

type ConTyFn = Tm.VAL



vToUnifForm :: Int -> Common.Value_ -> Tm.VAL
vToUnifForm ii val = case val of
  Common.VLam_ f ->
    let
      freeVar = Common.vfree_ $ Common.Quote ii
      funBody = f freeVar
      boundNom = LN.integer2Name $ toInteger ii
    in
      Tm.lam boundNom $ vToUnifForm (ii+1) funBody
  Common.VStar_ ->
    Tm.SET
  Common.VPi_ s f ->
    let
      freeVar = Common.vfree_ $ Common.Quote ii
      funBody = f freeVar
      boundNom = LN.integer2Name $ toInteger ii
    in
      Tm.PI (vToUnifForm ii s) (Tm.lam boundNom $ vToUnifForm (ii+1) funBody)
  Common.VNeutral_ neut ->
    let
      (headVar, args) = neutralToSpine ii neut
    in
      Tm.N headVar args

  Common.VNat_ ->
    Tm.Nat

  Common.VVec_ t1 t2 ->
    Tm.Vec (vToUnifForm ii t1) (vToUnifForm ii t2)

  Common.VEq_ t1 t2 t3 ->
    Tm.Eq (vToUnifForm ii t1) (vToUnifForm ii t2) (vToUnifForm ii t3)


neutralToHead :: Int -> Common.Neutral_ -> Tm.Head
neutralToHead ii neut = case neut of
  Common.NFree_ nm -> case nm of
    Common.Global s ->
      Tm.Var (LN.string2Name s) Tm.Only
    Common.Local i ->
      Tm.Var (LN.integer2Name $ toInteger $ ii - i) Tm.Only
    Common.Quote i ->
      Tm.Var (LN.integer2Name $ toInteger $ ii - i) Tm.Only

neutralToSpine ii neut = case neut of
  Common.NApp_ f x ->
    let
      (nhead, args) = neutralToSpine ii f
    in
      (nhead, args ++ [valToElim ii x])

  Common.NNatElim_ m mz ms n ->
    let
      (nhead, elims) = neutralToSpine ii n
      newElim = Tm.NatElim (vToUnifForm ii m) (vToUnifForm ii mz) (vToUnifForm ii ms)
    in
      (nhead, [newElim] ++ elims) --TODO which side of list?

  Common.NNatElim_ m mz ms n ->
    let
      (nhead, elims) = neutralToSpine ii n
      newElim = Tm.NatElim (vToUnifForm ii m) (vToUnifForm ii mz) (vToUnifForm ii ms)
    in
      (nhead, [newElim] ++ elims)

  Common.NVecElim_ a m mn mc n xs ->
    let
      (nhead, elims) = neutralToSpine ii xs
      newElim = Tm.VecElim (vToUnifForm ii a) (vToUnifForm ii m) (vToUnifForm ii mn)
        (vToUnifForm ii mc) (vToUnifForm ii n)
    in
      (nhead, [newElim] ++ elims)

  Common.NEqElim_ a m mr x y eq ->
    let
      (nhead, elims) = neutralToSpine ii eq
      newElim = Tm.EqElim (vToUnifForm ii a) (vToUnifForm ii m) (vToUnifForm ii mr)
        (vToUnifForm ii x) (vToUnifForm ii y)
    in
      (nhead, [newElim] ++ elims)

  _ -> (neutralToHead ii neut, [])

valToElim :: Int -> Common.Value_ -> Tm.Elim
valToElim ii val =
  Tm.A $ vToUnifForm ii val


unifToValue :: Tm.VAL -> Common.Value_
unifToValue val = case val of
  Tm.L _ ->
    Common.VLam_ $ \v ->
      unifToValue $ val Tm.$$ (vToUnifForm 0 v)

  Tm.SET ->
    Common.VStar_

  Tm.PI s t ->
    Common.VPi_ (unifToValue s) $ \x ->
      unifToValue $ t Tm.$$ (vToUnifForm 0 x)

  Tm.SIG s t -> error "TODO sigma"

  Tm.PAIR s t -> error "TODO sigma pair"

  Tm.N (Tm.Var nm Tm.Only) elims ->
    let
      subArgs = map elimToValue elims
      newHead = Common.NFree_ (Common.Global $ LN.name2String nm)
    in
      Common.VNeutral_ $ foldl Common.NApp_ newHead subArgs

  Tm.Nat ->
    Common.VNat_

  Tm.Vec t1 t2 ->
    Common.VVec_ (unifToValue t1) (unifToValue t2)

  Tm.Eq t1 t2 t3  ->
    Common.VEq_ (unifToValue t1) (unifToValue t2) (unifToValue t3)

  _ -> error "TODO twins, etc. should never happen"


elimToValue (Tm.A v) = unifToValue v

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

type ConstrContext = [(Common.Name, Tm.VAL)]
type WholeEnv = (Common.NameEnv Common.Value_, ConstrContext)



instance Show (UF.Point a) where
  show _ = "var"



--Initially, the only constraint we express is that two types unify
data Constraint =
  Constraint Common.Region (UC.Entry)

maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (h:_) = Just h




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


instance Unifyable Tm.VAL where
  fresh = metaFromInt <$> freshInt
  unify v1 v2 env = do
    tType <- metaFromInt <$> freshInt
    probId <- (UC.ProbId . LN.integer2Name . toInteger) <$> freshInt
    let newCon = UC.Unify $ UC.EQN tType v1 tType v2
    let ourEntry = UC.Prob probId newCon UC.Active
    addConstr $ Constraint (error "TODO region") ourEntry




type ConType = Tm.VAL


type ConstraintM a = WriterT [Constraint] (StateT [Int] Identity) a

--Operations in our monad:
--Make fresh types, and unify types together
freshVar :: ConstraintM Tm.VAL
freshVar = do
  newInt <- freshInt
  --newPoint <- lift $ lift $ UF.fresh BlankSlate
  return $  error "TODO fresh Metavariable from Int"


freshInt :: ConstraintM Int
freshInt = do
  (h:t) <- lift $ get
  put t
  return h



--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = tell [c]


metaFromInt ti = Tm.mv $ "--metaVar" ++ show ti

evaluate :: Common.CTerm_ -> WholeEnv -> ConstraintM ConType
evaluate term env@(nameEnv, context) = do
  t <- fresh
  let realContext = error "TODO realContext"
  let normalForm = Common.cEval_ term (nameEnv, realContext)
  unify t (error "TODO evaluate") env --cToUnifForm0 term
  return t

unknownIdent :: String -> ConstraintM a
unknownIdent s = error $ "Unknown Identifier: " ++ show s



mkEq :: ConType -> ConType -> ConType -> ConType
mkEq = error "TODO equality type"


tyFn :: (ConType -> ConType) -> ConType
tyFn f =
  let
    allVars :: [Tm.Nom]
    allVars = map LN.integer2Name [1..]
    dummyBody = f (Tm.var $ LN.integer2Name 0)
    freeVars :: [Tm.Nom]
    freeVars = Tm.fvs dummyBody
    newFreeVar = head $ filter (not . (`elem` freeVars)) allVars
  in
    Tm.lam newFreeVar (f $ Tm.var newFreeVar)


--conTyFn :: (Common.Type_ -> ConType) -> ConTyFn
--conTyFn f = error "TODO conTyFn"


applyVal :: ConType -> ConType -> ConType
applyVal = (Tm.$$)


applyPi :: ConTyFn -> ConType -> ConType
applyPi = applyVal

mkPi :: ConType -> ConTyFn -> ConType
mkPi = error "TODO mkPi"

conType :: Common.Type_ -> ConType
conType = vToUnifForm 0

mkVec = error "TODO mkVec"

--liftConTyFn :: (Common.Type_ -> Common.Type_) -> ConTyFn
--liftConTyFn f = error "TODO liftConTy"
