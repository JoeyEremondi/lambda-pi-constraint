{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, PatternSynonyms #-}
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

import System.IO.Unsafe (unsafePerformIO)

import qualified Data.Foldable as Foldable

import qualified Data.Maybe as Maybe

import Control.Applicative

import qualified Data.List as List

import qualified Unbound.Generics.LocallyNameless as LN

import qualified PatternUnify.Tm as Tm

import qualified PatternUnify.Context as UC

import qualified PatternUnify.Test as PUtest

import Control.Monad.Identity (runIdentity)

import Debug.Trace (trace)

import qualified Data.Map as Map

import Text.PrettyPrint.HughesPJ hiding (parens, ($$))

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
  , sourceMetas :: [String]
  --, quantParams :: [(Tm.Nom, Tm.VAL)]
  }

getRegionDict :: [Constraint] -> Map.Map Tm.Nom Common.Region
getRegionDict = foldr foldFun $ Map.singleton (LN.string2Name "builtinLoc") (Common.BuiltinRegion)
  where
    foldFun cstr dictSoFar =
      case conEntry cstr of
        (UC.Prob (UC.ProbId ident) _ _) ->
          Map.insert ident (conRegion cstr) dictSoFar
        _ ->
          dictSoFar


evalInEnv :: WholeEnv -> Tm.VAL -> ConstraintM Tm.VAL
evalInEnv env =
  Tm.eval $ Map.fromList $ map (\(s,val) -> (LN.s2n s, val)) $ globalValues env


evalElimInEnv :: WholeEnv -> Tm.Elim -> ConstraintM Tm.Elim
evalElimInEnv env =
  Tm.mapElimM $ Tm.eval $ Map.fromList $ map (\(s,val) -> (LN.s2n s, val)) $ globalValues env


addValue :: (Int, Tm.VAL) -> WholeEnv -> WholeEnv
addValue x env = env {valueEnv = x : valueEnv env }

addType :: (Int, Tm.VAL) -> WholeEnv -> WholeEnv
addType x env = env {typeEnv = x : typeEnv env }

recordSourceMeta :: String -> ConstraintM ()
recordSourceMeta nm = lift $ (modify $ \x -> x {sourceMetas = (nm : sourceMetas x)} )

runConstraintM :: ConstraintM a -> a
runConstraintM cm =
  fst $ fst $  runIdentity $ runStateT (runWriterT (LN.runFreshMT cm)) (ConstrainState [1..] []  )

solveConstraintM :: ConstraintM Tm.Nom -> Either [(Common.Region, String)] (Tm.VAL, [(String, Tm.VAL)])
solveConstraintM cm =
  let
    ((nom, constraints), cstate) = runIdentity $ runStateT (runWriterT (LN.runFreshMT cm)) (ConstrainState [1..] [] )
    regionDict = getRegionDict constraints
    ret = do
      (_, context) <- PUtest.solveEntries $ map conEntry constraints
      let finalType = evalState (UC.metaValue nom) context
      let solvedMetas =
            map (\sourceNom -> (sourceNom, evalState (UC.metaValue $ LN.s2n sourceNom) context)) $
              sourceMetas cstate
      return (finalType, solvedMetas)
  in case ret of
      Left pairs -> Left $ map (\(UC.ProbId ident, msg) -> (regionDict Map.! ident, msg)) pairs
      Right x -> Right x



cToUnifForm0 = cToUnifForm 0



evaluate :: Int -> Common.CTerm_ -> WholeEnv -> ConstraintM Tm.VAL
--evaluate ii t _ | trace ("EVAL!! " ++ show (ii, Common.cPrint_ 0 0 t)) False = error "eval"
evaluate ii t g = do
  result <- cToUnifForm ii g t
  evalInEnv g result
  --fst <$> LN.freshen result

cToUnifForm :: Int -> WholeEnv -> Common.CTerm_ -> ConstraintM Tm.VAL
cToUnifForm ii env tm'@(Common.L _ tm) = --trace ("CTO " ++ render (Common.cPrint_ 0 ii tm') ) $
 let
  result =
    case tm of
      Common.Inf_ itm -> --Here we bind a new variable, so increase our counter
        iToUnifForm ii env itm
      Common.Lam_ ctm -> do

        newNom <- freshNom $ localName (ii) --LN.s2n ("lamVar" ++ show ii)
          --(globals, boundVars) = env
        let newEnv = addValue (ii, Tm.var newNom) env -- (globals, (Common.Local ii, Tm.var newNom) : boundVars)
        retBody <- cToUnifForm (ii + 1) newEnv ctm
        return $ Tm.L $ LN.bind newNom retBody

      Common.Zero_ ->
        return $ Tm.Zero

      Common.Succ_ n ->
        Tm.Succ <$> cToUnifForm ii env n

      Common.FZero_ n ->
        Tm.FZero <$> cToUnifForm ii env n

      Common.FSucc_ n f ->
        Tm.FSucc <$> (cToUnifForm ii env n) <*> (cToUnifForm ii env f)

      Common.Nil_ tp ->
        Tm.VNil <$> cToUnifForm ii env tp

      Common.Cons_ a n x xs ->
        Tm.VCons <$> (cToUnifForm ii env a) <*> (cToUnifForm ii env n)
            <*> (cToUnifForm ii env x) <*> (cToUnifForm ii env xs)

      Common.Refl_ a x ->
        Tm.ERefl <$> (cToUnifForm ii env a) <*> (cToUnifForm ii env x)
  in result -- trace ("\n**CToUnif" ++ show ii ++ " " ++ show tm ++ "\nResult:" ++ show result) result


listLookup l i =
  if (i >= length l)
  then error $ "No elem " ++ show i ++ " in" ++ show l
  else l List.!! i

--The name for a local variable i at depth ii
localName :: Int -> String
localName ii = --TODO get fresh properly
  --LN.string2Name $
    case ii of
      0 -> "xx_"
      1 -> "yy_"
      2 -> "zz_"
      ourIndex ->  ( "local" ++ show ourIndex ++ "_")


iToUnifForm :: Int -> WholeEnv -> Common.ITerm_ -> ConstraintM Tm.VAL
iToUnifForm ii env ltm@(Common.L _ tm) = --trace ("ITO " ++ render (Common.iPrint_ 0 ii ltm)) $
    case tm of
      --TODO look at type during eval?
      Common.Meta_ nm ->
        return $ Tm.meta $ LN.string2Name nm
      Common.Ann_ val _ ->
        cToUnifForm ii env val

      Common.Star_ ->
        return Tm.SET

      Common.Pi_ s t@(Common.L tReg _) -> do
        freeNom <- freshNom $ localName ii
        let localVal = Tm.var freeNom
        sVal <- (cToUnifForm ii env s)
          --Our argument in t function has type S
        let
          newEnv = addValue (ii, Tm.var freeNom) $ addType (ii, sVal) env
        translatedFn <- (cToUnifForm (ii + 1) newEnv t)
          --tFn = Common.L tReg $ Common.Lam_ t --Bind over our free variable, since that's what Unif is expecting
        return $ Tm.PI sVal (Tm.lam freeNom translatedFn) --Close over our localVal in lambda
          --mkPiFn (cToUnifForm ii env s) (\x -> cToUnifForm (ii+1) (newEnv x) t)

      Common.Bound_ i ->
        let
          result = snd $ (valueEnv env `listLookup` i )
        in --trace ("Lookup ii" ++ show ii ++ " i " ++ show i ++ " as " ++ Tm.prettyString result ++ "\n  env: " ++ show (valueEnv env)) $
          return result

        --Tm.var $ localName (ii - i - 1) --Local name, just get the corresponding Nom
        --Tm.var $ deBrToNom ii i


      Common.Free_ (Common.Global nm) ->
        return $ Tm.vv nm --Keep things simple by not expanding globals
      --If we reach this point, then our neutral term isn't embedded in an application
      Common.Free_ fv ->
        case valueLookup fv env of
          Just x -> return  x
          Nothing ->
            return $ case fv of
              Common.Global nm -> trace ("Giving " ++ show nm ++ " global Nom " ++ Tm.prettyString (Tm.vv nm)) $
                Tm.vv nm
              Common.Local i ->
                error "LocalName should always be in env, Free_"
                --Tm.var $ localName i
              Common.Quote i ->
                error "Shouldn't come across quoted during checking"


      (f Common.:$: x) -> --trace ("APP " ++ show (Common.iPrint_ 0 ii f, Common.cPrint_ 0 ii x) ) $
        do
          f1 <- (iToUnifForm ii env f)
          a <- (cToUnifForm ii env x)
          fVal <- evalInEnv env f1
          aVal <- evalInEnv env a
          result <- --trace ("$ APP2 " ++ show (Tm.prettyString fVal, Tm.prettyString aVal))  $
                fVal Tm.$$ aVal
          --trace (
              --"APP  " ++ Tm.prettyString f1 ++ " <--- " ++ show f ++ "  \n  "
              -- ++ Tm.prettyString a ++ " <--- " ++ show x ++ "  \n  "
              -- ++ Tm.prettyString result) $
          --trace ("APP RESULT " ++ Tm.prettyString result) $
          return result

      Common.Nat_ ->
        return Tm.Nat

      Common.Fin_ n ->
        Tm.Fin <$> cToUnifForm ii env n

      Common.NatElim_ m mz ms n -> trace ("**NATELIM: " ++ show n) $ do
        spine <- Tm.NatElim <$> (cToUnifForm ii env m) <*> (cToUnifForm ii env mz) <*> (cToUnifForm ii env ms)
        hd <- (cToUnifForm ii env n)
        hdVal <- evalInEnv env hd
        spineVal <- evalElimInEnv env spine
        hdVal Tm.%% spineVal


      Common.FinElim_ m mz ms n f -> trace "%2" $  do
        hd <- (cToUnifForm ii env f)
        spine <- Tm.FinElim <$> (cToUnifForm ii env m) <*> (cToUnifForm ii env mz) <*> (cToUnifForm ii env ms) <*> (cToUnifForm ii env n)
        hdVal <- evalInEnv env hd
        spineVal <- evalElimInEnv env spine
        hdVal Tm.%% spineVal

      Common.Vec_ a n ->
        Tm.Vec <$> (cToUnifForm ii env a) <*> (cToUnifForm ii env n)

      Common.VecElim_ a m mn mc n xs -> trace "%3" $  do
        hd <- (cToUnifForm ii env xs)
        spine <- Tm.VecElim <$> (cToUnifForm ii env a) <*> (cToUnifForm ii env m) <*> (cToUnifForm ii env mn) <*> (cToUnifForm ii env mc) <*> (cToUnifForm ii env n)
        hdVal <- evalInEnv env hd
        spineVal <- evalElimInEnv env spine
        hdVal Tm.%% spineVal
      Common.Eq_ a x y ->
        Tm.Eq <$> (cToUnifForm ii env a) <*> (cToUnifForm ii env x) <*> (cToUnifForm ii env y)

      Common.EqElim_ a m mr x y eq  -> trace "%4" $ do
        hd <- (cToUnifForm ii env eq)
        spine <- Tm.EqElim <$> (cToUnifForm ii env a) <*> (cToUnifForm ii env m) <*> (cToUnifForm ii env mr) <*> (cToUnifForm ii env x) <*> (cToUnifForm ii env y)
        hdVal <- evalInEnv env hd
        spineVal <- evalElimInEnv env spine
        hdVal Tm.%% spineVal
--  in result --trace ("\n**ITO" ++ show ii ++ " " ++ show tm ++ "\nRESULT " ++ show result) result

type ConTyFn = Tm.VAL




splitContext :: [(Common.Name, a)] -> ([(String, a)], [(Int, a)])
splitContext entries = helper entries [] []
  where
    helper [] globals locals = (globals, locals)
    helper ( (Common.Global s, x) : rest) globals locals =
      helper rest ((s,x) : globals) locals
    helper ((Common.Local i, x) : rest) globals locals =
      helper rest globals ((i,x) : locals)



constrEval :: (Common.NameEnv Tm.VAL, Common.NameEnv Tm.VAL) -> Common.ITerm_ -> Tm.VAL
constrEval (tenv, venv) it =
  let
    tmSubs = map (\(Common.Global nm, v) -> (LN.s2n nm, v)) venv
    (tglobals, tlocals ) = splitContext tenv
    (vglobals, vlocals) = splitContext venv
    wholeEnv = WholeEnv vlocals tlocals vglobals tglobals
  in
    LN.runFreshM $ Tm.eval (Map.fromList tmSubs) $ runConstraintM (iToUnifForm 0 wholeEnv it)



--Initially, the only constraint we express is that two types unify
data Constraint =
  Constraint
    {conRegion :: Common.Region
    , conEntry :: UC.Entry }
    deriving (Show)

maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (h:_) = Just h


freshInt :: ConstraintM Int
freshInt = do
  oldState <- get
  let (i:newInts) = intStore oldState
  put $ oldState {intStore = newInts}
  return i

--We abstract over the environment
--And return a value which applies the local variables to it
fresh :: Common.Region -> WholeEnv -> Tm.VAL -> ConstraintM Tm.VAL
fresh reg env tp = do
    ourNom <- freshNom $ "α_" ++ Common.regionName reg ++ "__"
    let
      extendArrow (i,t) arrowSoFar =
        do
          --lNom <- freshNom $ localName i
          let Just (Tm.N ourVar _) = valueLookup (Common.Local i) env
              lNom = Tm.headVar ourVar
          return $ Tm._Pi lNom t arrowSoFar
    let currentQuants = reverse $ typeEnv env
        currentVals = reverse $ valueEnv env
        unsafeLook i = Maybe.fromJust $ valueLookup i env
    lambdaType <-
          Foldable.foldrM extendArrow tp (currentQuants) --TODO right order?
    --let ii = trace ("Made fresh lambda type " ++ PUtest.prettyString lambdaType)
    --      $ length (typeEnv env)
    let ourHead =
          --trace ("Lambda type " ++ PUtest.prettyString lambdaType ++ " with env " ++ show currentQuants) $
            Tm.Meta ourNom
    let ourElims = map (\(_,freeVal) -> Tm.A freeVal) currentVals
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
    probId <- UC.ProbId <$> freshNom "??"
    --TODO right to reverse?
    let currentQuants = reverse $ typeEnv env
        prob = UC.Unify $ UC.EQN tp v1 tp v2
    let newCon = --trace ("**WRAP " ++ Tm.prettyString prob ++ " QUANTS " ++ show currentQuants ) $
          wrapProblemForalls currentQuants env prob
    let ourEntry = UC.Prob probId newCon UC.Active
    addConstr $ Constraint reg  ourEntry

unifySets reg v1 v2 env = unify reg v1 v2 Tm.SET env

wrapProblemForalls :: [(Int, Tm.Type)] -> WholeEnv -> UC.Problem -> UC.Problem
wrapProblemForalls [] env prob = prob
wrapProblemForalls ((i, tp) : trest) env prob =
  let
    subVal = wrapProblemForalls trest env prob
    Just (Tm.N ourVar _) = valueLookup (Common.Local i) env
    ourNom = Tm.headVar ourVar
  in
    UC.All (UC.P tp) $ LN.bind ourNom subVal


freshType reg env = fresh reg env Tm.SET

type ConType = Tm.VAL


type ConstraintM = LN.FreshMT (WriterT [Constraint] (StateT ConstrainState Identity))


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

{-
freshInt :: ConstraintM Int
freshInt = do
  (h:t) <- lift $ intStore <$> get
  modify (\st -> st {intStore = t})
  return h
-}

freshNom :: String -> ConstraintM Tm.Nom
freshNom hint = do
  localId <- freshInt
  --let newHint = hint ++ show startNum ++ "_" ++ show localId ++ "_"
  LN.fresh $ LN.s2n hint
--freshNom hint = do
--  (h:t) <- lift $ intStore <$> get
--  modify (\st -> st {intStore = t})
--  return $ LN.string2Name $ hint ++ (show h)


--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = tell [c]
  --trace ("Adding constraint " ++ show c)$ tell [c]



unknownIdent :: Common.Region -> WholeEnv -> String -> ConstraintM a
unknownIdent reg env s = error $
  show reg ++ "Unknown IIdentifier: " ++ show s
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

mkPiFnM :: (LN.Fresh m) => ConType -> (ConType -> m ConType) -> m ConType
mkPiFnM s fm = do
  let
    allVars :: [Tm.Nom]
    allVars = map (\i -> LN.string2Name $ "tyPiFn" ++ show i ) [1..]
  dummyBody <-  fm (Tm.vv "dummy")
  let
    freeVars :: [Tm.Nom]
    freeVars = Tm.fvs dummyBody
    newFreeVar = head $ filter (not . (`elem` freeVars)) allVars
  arg <- (fm $ Tm.var newFreeVar)
  return $ Tm.PI s  $ Tm.lam newFreeVar  arg


--conType :: Common.Type_ -> ConType
--conType = vToUnifForm 0

mkVec :: ConType -> ConType -> ConType
mkVec = Tm.Vec

--liftConTyFn :: (Common.Type_ -> Common.Type_) -> ConTyFn
--liftConTyFn f = error "TODO liftConTy"
