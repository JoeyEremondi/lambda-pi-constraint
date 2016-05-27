{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Constraint where

import qualified Common
import Control.Monad.Identity (Identity)
import Control.Monad.State
import Control.Monad.Writer

import qualified Data.Foldable as Foldable

import qualified Data.Maybe as Maybe

import qualified Data.List as List

import qualified Unbound.Generics.LocallyNameless as LN

import qualified PatternUnify.Tm as Tm

import qualified PatternUnify.Check as Check
import qualified PatternUnify.Context as UC

import qualified PatternUnify.Run as Run

import Control.Monad.Identity (runIdentity)

import Debug.Trace (trace)

import qualified Data.Map as Map

import PatternUnify.Tm (Region (..))

import qualified Top.Implementation.TypeGraph.Basics as TGBasic

type ConstrContext = [(Common.Name, Tm.VAL)]

data WholeEnv =
  WholeEnv
  { valueEnv     :: [(Int, Tm.VAL)]
  , typeEnv      :: [(Int, Tm.VAL)]
  , globalValues :: [(String, Tm.VAL)]
  , globalTypes  :: [(String, Tm.VAL)]
  } deriving (Show)

typeLookup :: Common.Name -> WholeEnv -> Maybe Tm.VAL
typeLookup (Common.Global s) env = List.lookup s (globalTypes env)
typeLookup (Common.Local i) env =
  List.lookup i (typeEnv env)
typeLookup (Common.Quote x) _ = error $ "Cannot lookup quoted value " ++ show x

valueLookup :: Common.Name -> WholeEnv -> Maybe Tm.VAL
valueLookup (Common.Global s) env = List.lookup s (globalValues env)
valueLookup (Common.Local i) env =
  List.lookup i (valueEnv env)
valueLookup (Common.Quote x) _ = error $ "Cannot lookup quoted value " ++ show x

data ConstrainState =
  ConstrainState
  { intStore      :: [Int]
  , sourceMetas   :: [Tm.Nom]
  , metaLocations :: Map.Map Tm.Nom Region
  --, quantParams :: [(Tm.Nom, Tm.VAL)]
  }

-- getRegionDict :: [Constraint] -> Map.Map Tm.Nom Region
-- getRegionDict = foldr foldFun $ Map.singleton (LN.string2Name "builtinLoc") (Common.BuiltinRegion)
--   where
--     foldFun cstr dictSoFar =
--       case conEntry cstr of
--         (UC.Prob (UC.ProbId ident) _ _) ->
--           Map.insert ident (conRegion cstr) dictSoFar
--         _ ->
--           dictSoFar


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

recordSourceMeta :: Region -> Tm.Nom -> ConstraintM ()
recordSourceMeta reg nm = do
  lift $ (modify $ \x -> x {sourceMetas = (nm : sourceMetas x)
                           ,metaLocations = Map.insert nm reg  $ metaLocations x } )

recordTypeMeta :: Region -> Tm.Nom -> ConstraintM ()
recordTypeMeta reg nm = do
  lift $ (modify $ \x -> x {metaLocations = Map.insert nm reg  $ metaLocations x } )

runConstraintM :: ConstraintM a -> a
runConstraintM cm =
  fst $ fst $  runIdentity $ runStateT (runWriterT (LN.runFreshMT cm)) (ConstrainState [1..] [] Map.empty  )

--Filter out things that don't affect unification because they have no vars
constrReflexive :: UC.Entry -> Bool
constrReflexive e@(UC.Prob _ (UC.Unify (UC.EQN Tm.SET s Tm.SET t _)) _ _ ) =
  (null $ Tm.fmvs s ++ Tm.fmvs t) && s == t
constrReflexive _ = False

solveConstraintM :: ConstraintM (Tm.Nom, Tm.VAL) -> Either [(Region, String)] (Tm.Type, Tm.VAL, Tm.Subs, Map.Map Tm.Nom Region)
solveConstraintM cm =
  let
    getCL (cl, _, _, _, _, _) = cl
    (((nom, normalForm), rawConstraints), cstate) = runIdentity $ runStateT (runWriterT (LN.runFreshMT cm)) (ConstrainState [1..] [] Map.empty )
    --regionDict = getRegionDict constraints
    ret = do
      (_, context@(cl, cr, probId, finalGraph,finalStr,_)) <-
        Run.solveEntries $ filter (not . constrReflexive) $  map conEntry rawConstraints
      let (unsolved, metaSubs) = UC.getUnsolvedAndSolved (cl)
      let finalType = Tm.unsafeFlatten $ evalState (UC.metaValue nom) context
      let sourceSubs = Map.map Tm.unsafeFlatten $ Map.filterWithKey (\k _ -> k `elem` sourceMetas cstate) metaSubs
      let finalSubs = UC.finalSub cl
      return (finalType, unsolved, sourceSubs)

  in
    case ret of
      Left (Run.ErrorResult ctx []) -> error "Left empty with Constraint ret solveResult"
      Left (Run.ErrorResult ctx solverErrs) ->
        let
          cl = getCL ctx
          finalSub = UC.finalSub cl
        in
          trace ("Final sub: " ++ List.intercalate "\n" (map show finalSub)) $ Left $ map (mkErrorPair finalSub ) solverErrs
        --Left $ map (\(UC.ProbId ident, msg) -> (regionDict Map.! ident, msg)) (mkErrorPairs solverErrs ((\(a,_,_,_,_) -> a) ctx) )
      Right (tp, [], subs) -> Right (tp, normalForm, subs, metaLocations cstate)
      Right (_, unsolved, _) -> --trace "solveConstraintM Right with unsolved" $
        Left $ case (filter (\(nom,_, _) -> nom `elem` (sourceMetas cstate)) unsolved ) of
          [] ->
              map (unsolvedMsg (sourceMetas cstate) ) unsolved
          sms -> map (unsolvedMsg (sourceMetas cstate) ) sms

--mkErrorPair :: Run.SolverErr -> (Region, String)
mkErrorPair finalSub (Run.StringErr (UC.ProbId ident, reg, msg)) = (reg, msg)
mkErrorPair finalSub (Run.GraphErr edgeInfos) =
  (UC.infoRegion $ UC.edgeEqnInfo $ snd $ head edgeInfos,
  "Cannot solve the following constraints:\n"
  ++ concatMap (edgeMessage finalSub ) edgeInfos)

edgeMessage :: Tm.SubsList -> ([TGBasic.EdgeId], UC.ConstraintInfo) -> String
edgeMessage finalSub (edgeId, edgeInfo) =
  "  " ++ (Common.prettySource $ UC.infoRegion $ UC.edgeEqnInfo edgeInfo)
  ++ " " ++ constrStr ++ "\n"
  where
    (s,t) = UC.edgeEqn edgeInfo
    constrStr = Tm.prettyString s ++ " === " ++ Tm.prettyString t
    -- constrStr = case (UC.edgeType edgeInfo) of
    --   (UC.InitConstr _) -> Tm.prettyString s ++ " === " ++ Tm.prettyString t ++ "(initial)" -- Tm.prettyString prob
    --   -- (UC.DefnUpdate c) -> "TODO1"
    --   -- (UC.ProbUpdate c) -> "TODO2"
    --   (UC.DefineMeta c) -> "TODO3"
    --   (UC.DerivedEqn _)  ->
    --     Tm.prettyString (Tm.unsafeFlatten $ LN.substs finalSub s) ++ " === " ++    Tm.prettyString (Tm.unsafeFlatten $ LN.substs finalSub t) ++ "(derived)"
    --   (UC.ChoiceEdge _ alpha (s,t)) -> Tm.prettyString s ++ " === " ++ Tm.prettyString t ++ "(choice)"


unsolvedMsg :: [Tm.Nom] -> (Tm.Nom, Region, Maybe Tm.VAL) -> (Region, String)
unsolvedMsg sourceMetas (nm,reg,_) | not (nm `elem` sourceMetas) =
  ( reg
  , show nm ++ " Could not infer type. Try adding type annotations, or report this as a bug.")
unsolvedMsg sourceMetas (nm,reg,Nothing) =
  ( reg
  , show nm ++ " Could deduce no information about metavariable " ++ (drop 2 $ show nm)
  ++  ". Try adding type annotations, or giving explicit arguments.")
unsolvedMsg sourceMetas (nm,reg,(Just val)) =
  (reg
  , "Metavariable " ++ (drop 2 $ show nm) ++ " has the form "
    ++ Tm.prettyString val
    ++ " for some unconstrained variables. Try adding an annotation or giving explicit arguments. "
    ++ List.intercalate " " (map Tm.prettyString $ Tm.fmvs val) )


cToUnifForm0 = cToUnifForm 0



evaluate :: Int -> Common.CTerm_ -> WholeEnv -> ConstraintM Tm.VAL
--evaluate ii t _ | trace ("EVAL!! " ++ show (ii, Common.cPrint_ 0 0 t)) False = error "eval"
evaluate ii t g = do
  result <- cToUnifForm ii g t
  evalInEnv g result

cToUnifForm :: Int -> WholeEnv -> Common.CTerm_ -> ConstraintM Tm.VAL
cToUnifForm ii env tm'@(Common.L _ tm) = --trace ("CTO " ++ render (Common.cPrint_ 0 ii tm') ) $
 let
  result =
    case tm of
      Common.Inf_ itm -> --Here we bind a new variable, so increase our counter
        iToUnifForm ii env itm
      Common.Lam_ ctm -> do

        newNom <- freshNom $ localName (ii) --LN.s2n ("lamVar" ++ show ii)
        let newEnv = addValue (ii, Tm.var newNom) env -- (globals, (Common.Local ii, Tm.var newNom) : boundVars)
        retBody <- cToUnifForm (ii + 1) newEnv ctm
        return $ Tm.L $ LN.bind newNom retBody

      Common.Pair_ x y ->
        Tm.PAIR <$> cToUnifForm ii env x <*> cToUnifForm ii env y

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
localName ii =
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
        return $ applyEnvToNom (LN.string2Name nm) env
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
        return $ Tm.PI sVal (Tm.lam freeNom translatedFn) --Close over our localVal in lambda

      Common.Sigma_ s t@(Common.L tReg _) -> do
        freeNom <- freshNom $ localName ii
        let localVal = Tm.var freeNom
        sVal <- (cToUnifForm ii env s)
          --Our argument in t function has type S
        let
          newEnv = addValue (ii, Tm.var freeNom) $ addType (ii, sVal) env
        translatedFn <- (cToUnifForm (ii + 1) newEnv t)
        return $ Tm.SIG sVal (Tm.lam freeNom translatedFn) --Close over our localVal in lambda

      Common.Bound_ i ->
        let
          result = snd $ (valueEnv env `listLookup` i )
        in --trace ("Lookup ii" ++ show ii ++ " i " ++ show i ++ " as " ++ Tm.prettyString result ++ "\n  env: " ++ show (valueEnv env)) $
          return result


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
          result <-
                fVal Tm.$$ aVal
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

      Common.Fst_ x -> do
        pr <- iToUnifForm ii env x
        prVal <- evalInEnv env pr
        pr Tm.%% Tm.Hd

      Common.Snd_ x -> do
        pr <- iToUnifForm ii env x
        prVal <- evalInEnv env pr
        pr Tm.%% Tm.Tl

type ConTyFn = Tm.VAL




splitContext :: [(Common.Name, a)] -> ([(String, a)], [(Int, a)])
splitContext entries = helper entries [] []
  where
    helper [] globals locals = (globals, locals)
    helper ( (Common.Global s, x) : rest) globals locals =
      helper rest ((s,x) : globals) locals
    helper ((Common.Local i, x) : rest) globals locals =
      helper rest globals ((i,x) : locals)
    helper _ _ _ = undefined



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
    {conRegion :: Region
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
fresh :: Region -> WholeEnv -> Tm.VAL -> ConstraintM Tm.VAL
fresh reg env tp = do
    ourNom <- freshNom $ "α_" ++ Common.regionName reg ++ "__"
    recordTypeMeta reg ourNom
    declareWithNom reg env tp ourNom


declareWithNom :: Region -> WholeEnv -> Tm.Type -> Tm.Nom -> ConstraintM Tm.VAL
declareWithNom reg env tp ourNom = do
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
  let ourHead =
        --trace ("Lambda type " ++ Run.prettyString lambdaType ++ " with env " ++ show currentQuants) $
          Tm.Meta ourNom
  let ourEntry = --trace ("Made fresh meta app " ++ Run.prettyString ourNeutral ++ "\nQnuant list " ++ show currentQuants) $
        UC.E ourNom lambdaType UC.HOLE (UC.EqnInfo UC.Initial reg UC.Factual)
  addConstr $ Constraint Common.startRegion ourEntry
  return $ applyEnvToNom ourNom env

applyEnvToNom ourNom env =
  let
    currentVals = reverse $ valueEnv env
    ourElims = map (\(_,freeVal) -> Tm.A freeVal) currentVals
    ourHead = Tm.Meta ourNom
  in
    Tm.N ourHead ourElims

freshTopLevel :: Tm.VAL -> ConstraintM Tm.Nom
freshTopLevel tp = do
    ourNom <- freshNom "topLevel"
    let ourEntry =
          UC.E ourNom tp UC.HOLE (UC.EqnInfo UC.Initial BuiltinRegion UC.Factual)
    addConstr $ Constraint Common.startRegion ourEntry
    return ourNom

unify :: Region -> Tm.VAL -> Tm.VAL -> Tm.VAL -> WholeEnv -> ConstraintM ()
unify reg v1 v2 tp env = do
    probId <- UC.ProbId <$> freshNom ("??_" ++ Common.regionName reg ++ "_")
    --TODO right to reverse?
    let currentQuants = reverse $ typeEnv env
        prob = UC.Unify $ UC.EQN tp v1 tp v2 (UC.EqnInfo UC.Initial reg UC.Factual)
    let newCon = --trace ("**WRAP " ++ Tm.prettyString prob ++ " QUANTS " ++ show currentQuants ) $
          wrapProblemForalls currentQuants env prob
    let ourEntry = UC.Prob probId newCon UC.Active []
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


freshNom :: String -> ConstraintM Tm.Nom
freshNom hint = do
  localId <- freshInt
  LN.fresh $ LN.s2n hint


--Helpful utility function
addConstr :: Constraint -> ConstraintM ()
addConstr c = tell [c]
  --trace ("Adding constraint " ++ show c)$ tell [c]



unknownIdent :: Region -> WholeEnv -> String -> ConstraintM a
unknownIdent reg env s = error $
  show reg ++ "Unknown Identifier: " ++ show s
  -- ++ " in env " ++ show env



mkEq :: ConType -> ConType -> ConType -> ConType
mkEq = Tm.Eq


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

mkVec :: ConType -> ConType -> ConType
mkVec = Tm.Vec
