{-# LANGUAGE FlexibleInstances, PatternSynonyms #-}
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
import Control.Monad.Identity (Identity)
import Control.Monad.State
import Control.Monad.Trans
import qualified Control.Monad.Trans.UnionFind as UF
import Control.Monad.Writer
import Data.Data
import Data.Typeable

import Control.Applicative

import qualified Data.List as List

import qualified Unbound.LocallyNameless as LN

import qualified PatternUnify.Tm as Tm

import qualified PatternUnify.Context as UC

import qualified PatternUnify.Test as PUtest

import Control.Monad.Identity (runIdentity)

import Debug.Trace (trace)

type ConstrContext = [(Common.Name, Tm.VAL)]

data WholeEnv =
  WholeEnv
  { valueEnv     :: [(Int, Tm.VAL)]
  , typeEnv :: [(Int, Tm.VAL)]
  , globalValues :: [(String, Tm.VAL)]
  , globalTypes :: [(String, Tm.VAL)]
  } deriving (Show)

typeLookup :: Common.Name -> WholeEnv -> Maybe Tm.VAL
typeLookup (Common.Global s) env = List.lookup s (globalTypes env)
typeLookup (Common.Local i) env =
  List.lookup i (typeEnv env)

valueLookup :: Common.Name -> WholeEnv -> Maybe Tm.VAL
valueLookup (Common.Global s) env = List.lookup s (globalValues env)
valueLookup (Common.Local i) env =
  List.lookup i (valueEnv env)

data ConstrainState =
  ConstrainState
  { intStore :: [Int]
  --, quantParams :: [(Tm.Nom, Tm.VAL)]
  }


addValue :: (Int, Tm.VAL) -> WholeEnv -> WholeEnv
addValue x env = env {valueEnv = x : valueEnv env }

addType :: (Int, Tm.VAL) -> WholeEnv -> WholeEnv
addType x env = env {typeEnv = x : typeEnv env }

solveConstraintM :: ConstraintM Tm.Nom -> Either String Tm.VAL
solveConstraintM cm = do
    let ((nom, constraints), _) = runIdentity $ runStateT (runWriterT cm) (ConstrainState [1..] )
    (_, context) <- PUtest.solveEntries $ map conEntry constraints
    return $ evalState (UC.metaValue nom) context



cToUnifForm0 = cToUnifForm 0

cToUnifForm :: Int -> WholeEnv -> Common.CTerm_ -> Tm.VAL
cToUnifForm ii env (Common.L _ tm) =
 let
  result =
    case tm of
      Common.Inf_ itm -> --Here we bind a new variable, so increase our counter
        iToUnifForm ii env itm
      Common.Lam_ ctm ->
        let
          newNom = localName (ii+1) --LN.s2n ("lamVar" ++ show ii)
          --(globals, boundVars) = env
          newEnv = addType (ii, Tm.var newNom) env -- (globals, (Common.Local ii, Tm.var newNom) : boundVars)
          retBody = cToUnifForm (ii + 1) newEnv ctm
        in
          Tm.L $ LN.bind newNom retBody

      Common.Zero_ ->
        Tm.Zero

      Common.Succ_ n ->
        Tm.Succ $ cToUnifForm ii env n

      Common.Nil_ tp ->
        Tm.VNil $ cToUnifForm ii env tp

      Common.Cons_ a n x xs ->
        Tm.VCons (cToUnifForm ii env a) (cToUnifForm ii env n)
            (cToUnifForm ii env x) (cToUnifForm ii env xs)

      Common.Refl_ a x ->
        Tm.ERefl (cToUnifForm ii env a) (cToUnifForm ii env x)
  in result -- trace ("\n**CToUnif" ++ show ii ++ " " ++ show tm ++ "\nResult:" ++ show result) result

--deBrToNom :: Int -> Int -> Tm.Nom
--deBrToNom ii i = LN.integer2Name $ toInteger $ ii - i

listLookup l i =
  if (i >= length l)
  then error $ "No elem " ++ show i ++ " in" ++ show l
  else l List.!! i

--The name for a local variable i at depth ii
localName :: Int -> Tm.Nom
localName ii =
  LN.string2Name $ case ii of
      0 -> "x"
      1 -> "y"
      2 -> "z"
      ourIndex ->  ( "local" ++ show ourIndex)


iToUnifForm :: Int -> WholeEnv -> Common.ITerm_ -> Tm.VAL
iToUnifForm ii env ltm@(Common.L _ tm) = --trace ("ito " ++ show ltm) $
  let
   result =
    case tm of
      --TODO look at type during eval?
      Common.Meta_ nm ->
        Tm.meta $ LN.string2Name nm
      Common.Ann_ val tp ->
        cToUnifForm ii env val

      Common.Star_ ->
        Tm.SET

      Common.Pi_ s t@(Common.L tReg _) ->
        let
           --(fst env, (Common.Local ii, x) : snd env)
          freeNom =  localName (ii+1)
          localVal = Tm.var freeNom
          sVal = (cToUnifForm ii env s)
          --Our argument in t function has type S
          newEnv = addType (ii, sVal) env
          translatedFn = (cToUnifForm (ii + 1) newEnv t)
          --tFn = Common.L tReg $ Common.Lam_ t --Bind over our free variable, since that's what Unif is expecting
        in Tm.PI sVal (Tm.lam freeNom translatedFn) --Close over our localVal in lambda
          --mkPiFn (cToUnifForm ii env s) (\x -> cToUnifForm (ii+1) (newEnv x) t)

      Common.Bound_ i -> --trace ("Lookup ii" ++ show ii ++ " i " ++ show i) $
        --snd $ (typeEnv env `listLookup` (ii - i ) )
        Tm.var $ localName (ii - i) --Local name, just get the corresponding Nom
        --Tm.var $ deBrToNom ii i

      --If we reach this point, then our neutral term isn't embedded in an application
      Common.Free_ fv ->
        case valueLookup fv env of
        Just x -> x
        Nothing ->
            case fv of
              Common.Global nm ->
                Tm.vv nm
              Common.Local i ->
                Tm.var $ localName i --Take our current depth, minus deBruijn index
              Common.Quote i ->
                error "Shouldn't come across quoted during checking"


      (f Common.:$: x) ->
        (iToUnifForm ii env f) Tm.$$ (cToUnifForm ii env x)

      Common.Nat_ ->
        Tm.Nat

      Common.NatElim_ m mz ms n ->
        (cToUnifForm ii env n) Tm.%%%
          [Tm.NatElim (cToUnifForm ii env m) (cToUnifForm ii env mz) (cToUnifForm ii env ms)]

      Common.Vec_ a n ->
        Tm.Vec (cToUnifForm ii env a) (cToUnifForm ii env n)

      Common.VecElim_ a m mn mc n xs ->
        (cToUnifForm ii env xs) Tm.%%%
          [Tm.VecElim (cToUnifForm ii env a) (cToUnifForm ii env m) (cToUnifForm ii env mn)
              (cToUnifForm ii env mc) (cToUnifForm ii env n)]

      Common.Eq_ a x y ->
        Tm.Eq (cToUnifForm ii env a) (cToUnifForm ii env x) (cToUnifForm ii env y)


      Common.EqElim_ a m mr x y eq  ->
        (cToUnifForm ii env eq) Tm.%%%
          [Tm.EqElim (cToUnifForm ii env a) (cToUnifForm ii env m) (cToUnifForm ii env mr)
              (cToUnifForm ii env x) (cToUnifForm ii env y)]
  in result --trace ("\n**ITO" ++ show ii ++ " " ++ show tm ++ "\nRESULT " ++ show result) result

type ConTyFn = Tm.VAL



vToUnifForm :: Int -> Common.Value_ -> Tm.VAL
vToUnifForm ii val = case val of
  Common.VLam_ f ->
    let
      freeVar = Common.vfree_ $ Common.Quote ii
      funBody = f freeVar
      boundNom = localName ii--LN.string2Name $ "local" ++ show ii
    in
      Tm.lam boundNom $ vToUnifForm (ii + 1) funBody
  Common.VStar_ ->
    Tm.SET
  Common.VPi_ s f ->
    let
      tyFnVal = (vToUnifForm (ii + 1)) . f . unifToValue
      varName = localName ii
      tyFn = Tm.lam varName $ tyFnVal (Tm.var varName)
    in
      Tm.PI (vToUnifForm ii s) tyFn
  Common.VNeutral_ neut ->
    let
      (headVar, args) = neutralToSpine ii neut
    in
      Tm.N headVar args

  Common.VNat_ ->
    Tm.Nat

  Common.VZero_ ->
    Tm.Zero

  Common.VSucc_ n ->
    Tm.Succ (vToUnifForm ii n)

  Common.VVec_ t1 t2 ->
    Tm.Vec (vToUnifForm ii t1) (vToUnifForm ii t2)

  Common.VNil_ tp ->
    Tm.VNil (vToUnifForm ii tp)

  --TODO other cases

  Common.VEq_ t1 t2 t3 ->
    Tm.Eq (vToUnifForm ii t1) (vToUnifForm ii t2) (vToUnifForm ii t3)



neutralToHead :: Int -> Common.Neutral_ -> Tm.Head
neutralToHead ii neut = case neut of
  Common.NFree_ nm -> case nm of
    Common.Global s ->
      Tm.Var (LN.string2Name s) Tm.Only
    Common.Local i ->
      error "Local should not occur in Neutrals"
    Common.Quote i ->
      Tm.Var (localName (ii-i)) Tm.Only

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







--Initially, the only constraint we express is that two types unify
data Constraint =
  Constraint
    {conRegion :: Common.Region
    , conEntry :: UC.Entry }
    deriving (Show)

maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (h:_) = Just h




--class Unifyable a where
--  unify :: a -> a -> WholeEnv -> ConstraintM ()
--  fresh :: Tm.VAL -> ConstraintM a



  --Define a "Constrain" monad, which lets us generate
  --new variables and store constraints in our state


{-data ConstraintState =
  ConstraintState
  { pointSupply :: UF.PointSupply TypeRepr
  , constraintsSoFar :: [Constraint]
  }-}

--We abstract over the environment
--And return a value which applies the local variables to it
fresh :: WholeEnv -> Tm.VAL -> ConstraintM Tm.VAL
fresh env tp = do
    ourNom <- freshNom "α_"
    let currentQuants = reverse $ typeEnv env
    let lambdaType =
          foldr (\(i, t) arrowSoFar -> Tm._Pi (localName i) t arrowSoFar)
            tp (currentQuants) --TODO right order?
    --let ii = trace ("Made fresh lambda type " ++ PUtest.prettyString lambdaType)
    --      $ length (typeEnv env)
    let ourHead =
          --trace ("Lambda type " ++ PUtest.prettyString lambdaType ++ " with env " ++ show currentQuants) $
            Tm.Meta ourNom
    let ourElims = map (\(i,_) -> Tm.A $ Tm.var $ localName i) currentQuants
    let ourNeutral = Tm.N ourHead ourElims
    let ourEntry = --trace ("Made fresh meta app " ++ PUtest.prettyString ourNeutral ++ "\nQnuant list " ++ show currentQuants) $
          UC.E ourNom lambdaType UC.HOLE
    addConstr $ Constraint Common.startRegion ourEntry
    return ourNeutral
    --let ourEntry =  UC.E ourNom tp UC.HOLE
    --addConstr $ Constraint Common.startRegion ourEntry
    --return $ Tm.meta ourNom

declareMeta :: Tm.Nom -> Tm.VAL -> ConstraintM ()
declareMeta ourNom tp = do
  let ourEntry =  UC.E ourNom tp UC.HOLE
  addConstr $ Constraint Common.startRegion ourEntry


metaNom :: String -> Tm.Nom
metaNom = LN.string2Name

freshTopLevel ::Tm.VAL -> ConstraintM Tm.Nom
freshTopLevel tp = do
    ourNom <- freshNom "topLevel"
    let ourEntry =
          UC.E ourNom tp UC.HOLE
    addConstr $ Constraint Common.startRegion ourEntry
    return ourNom

unify :: Common.Region -> Tm.VAL -> Tm.VAL -> Tm.VAL -> WholeEnv -> ConstraintM ()
unify reg v1 v2 tp env = do
    probId <- (UC.ProbId . LN.integer2Name . toInteger) <$> freshInt
    --TODO right to reverse?
    let currentQuants = reverse $ typeEnv env
    let newCon = wrapProblemForalls currentQuants
          $ UC.Unify $ UC.EQN tp v1 tp v2
    let ourEntry = UC.Prob probId newCon UC.Active
    addConstr $ Constraint reg  ourEntry

unifySets reg v1 v2 env = unify reg v1 v2 Tm.SET env

wrapProblemForalls :: [(Int, Tm.VAL)] -> UC.Problem -> UC.Problem
wrapProblemForalls [] prob = prob
wrapProblemForalls ((i, tp) : rest) prob =
  UC.All (UC.P tp) $ LN.bind (localName i) $ wrapProblemForalls rest prob

{-
forAllUnify
  :: LN.Name Tm.VAL
  -> Tm.VAL
  -> Tm.VAL
  -> Tm.VAL
  -> Tm.VAL
  -> WholeEnv
  -> ConstraintM ()
forAllUnify quantVar quantType v1 v2 tp env = do
    probId <- (UC.ProbId . LN.integer2Name . toInteger) <$> freshInt
    let newCon = UC.All (UC.P quantType) $ LN.bind quantVar $ UC.Unify $ UC.EQN tp v1 tp v2
    let ourEntry = UC.Prob probId newCon UC.Active
    addConstr $ Constraint (Common.startRegion) ourEntry
-}


freshType env = fresh env Tm.SET

type ConType = Tm.VAL


type ConstraintM a = WriterT [Constraint] (StateT ConstrainState Identity) a

--Operations in our monad:

{-
--Do the given computation with the given name added to our quantifier list
--Then remove it from the list when we're done
forallVar :: Tm.Nom -> Tm.VAL -> (ConstraintM a) -> ConstraintM a
forallVar nm tp cm = do
  modify (\st -> st {quantParams = (nm, tp) : quantParams st})
  result <- cm
  modify (\st -> st {quantParams = tail $ quantParams st})
  return result
-}

freshInt :: ConstraintM Int
freshInt = do
  (h:t) <- lift $ intStore <$> get
  modify (\st -> st {intStore = t})
  return h


freshNom :: String -> ConstraintM Tm.Nom
freshNom hint = do
  (h:t) <- lift $ intStore <$> get
  modify (\st -> st {intStore = t})
  return $ LN.string2Name $ hint ++ (show h)


--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = tell [c]
  --trace ("Adding constraint " ++ show c)$ tell [c]


--metaFromInt ti = Tm.mv $ "--metaVar" ++ show ti


evaluate :: Common.CTerm_ -> WholeEnv -> ConstraintM ConType
evaluate term env = do
  --t <- fresh (error "TODO type in eval")
  let normalForm = cToUnifForm 0 env term
  --unify t normalForm env --cToUnifForm0 term
  return normalForm

unknownIdent :: WholeEnv -> String -> ConstraintM a
unknownIdent env s = error $
  "Unknown Identifier: " ++ show s
  ++ " in env " ++ show env



mkEq :: ConType -> ConType -> ConType -> ConType
mkEq = Tm.Eq




--conTyFn :: (Common.Type_ -> ConType) -> ConTyFn
--conTyFn f = error "TODO conTyFn"



--mkPi :: ConType -> ConTyFn -> ConType
--mkPi = Tm._PI "piVar"


mkPiFn :: ConType -> (ConType -> ConType) -> ConType
mkPiFn s f =
  let
    allVars :: [Tm.Nom]
    allVars = map (\i -> LN.string2Name $ "tyPiFn" ++ show i ) [1..]
    dummyBody = f (Tm.vv "dummy")
    freeVars :: [Tm.Nom]
    freeVars = Tm.fvs dummyBody
    newFreeVar = head $ filter (not . (`elem` freeVars)) allVars
  in
    Tm.PI s  $ Tm.lam newFreeVar (f $ Tm.var newFreeVar)


--conType :: Common.Type_ -> ConType
--conType = vToUnifForm 0

mkVec :: ConType -> ConType -> ConType
mkVec = Tm.Vec

--liftConTyFn :: (Common.Type_ -> Common.Type_) -> ConTyFn
--liftConTyFn f = error "TODO liftConTy"
