--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

-- This module defines unification problems, metacontexts and operations
-- for working on them in the |Contextual| monad.

module PatternUnify.Context where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import qualified Control.Monad.Writer as Writer

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import Debug.Trace (trace)
import GHC.Generics

import Unbound.Generics.LocallyNameless hiding (join, restrict)
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
--import Unbound.LocallyNameless.Types (GenBind(..))

import PatternUnify.Kit
import PatternUnify.Tm

--import Debug.Trace (trace)

import Data.List (union)

import qualified Top.Implementation.TypeGraph.Standard as TG

import qualified Top.Interface.Basic as Basic

import qualified Top.Implementation.TypeGraph.ClassMonadic as CM

import qualified Top.Implementation.TypeGraph.ApplyHeuristics as Heur

import Top.Solver (LogEntries)

import Common (Region)
import Text.Parsec (SourcePos)

type BadEdges = [Heur.ErrorInfo ConstraintInfo]

type TypeGraph = TG.StandardTypeGraph ConstraintInfo

data Dec = HOLE | DEFN VAL
  deriving (Show, Generic)

instance Alpha Region
instance Subst VAL Region

instance Alpha Dec
instance Subst VAL Dec

instance Occurs Dec where
    occurrence _  HOLE      = Nothing
    occurrence xs (DEFN t)  = occurrence xs t
    frees _       HOLE      = []
    frees isMeta  (DEFN t)  = frees isMeta t

data EqnInfo =
  EqnInfo
  { creationInfo :: CreationInfo
  , infoRegion   :: Region
  , isCF         :: IsCF
  } deriving (Eq, Show, Generic)

data CreationInfo = Initial | CreatedBy ProbId
  deriving (Eq, Show, Generic)


data Equation = EQN Type VAL Type VAL EqnInfo
  deriving (Show, Generic)

instance Alpha Equation
instance Alpha EqnInfo
instance Subst VAL Equation
instance Subst VAL EqnInfo

instance Occurs Equation where
    occurrence xs (EQN _S s _T t _) = occurrence xs [_S, s, _T, t]
    frees isMeta (EQN _S s _T t _) = frees isMeta [_S, s, _T, t]

instance Pretty Equation where
  pretty (EQN _S s _T t _) =  f <$> (pretty _S) <*> (pretty s) <*> (pretty _T) <*> (prettyVal t)
      where f _S' s' _T' t' = parens (s' <+> colon <+> _S') <+>
                                  text "===" <+> parens (t' <+> colon <+> _T')
            prettyVal :: (Applicative m, LFresh m, MonadReader Size m) => VAL -> m Doc
            prettyVal v = pretty v

data ConstraintInfo = ConstraintInfo
  { edgeType    :: ConstraintType
  , edgeEqnInfo :: EqnInfo
  } deriving (Eq, Show, Generic)

data ConstraintType =
  InitConstr ProbId Problem
  | DefnUpdate Nom
  | ProbUpdate ProbId
  | DefineMeta Nom
  | DerivedEqn ProbId Problem
  deriving (Eq, Show, Generic)

data Problem  =  Unify Equation
              |  All Param (Bind Nom Problem)
  deriving (Show, Generic)

instance Alpha Problem
instance Eq Problem where
    (==) = aeq

instance Occurs Problem where
    occurrence xs (Unify q)        = occurrence xs q
    occurrence xs (All e (B _ p))  = max (occurrence xs e) (occurrence xs p)
    frees isMeta (Unify q)         = frees isMeta q
    frees isMeta (All e (B _ p))   = frees isMeta e `union` frees isMeta p

instance Subst VAL Problem where
    substs s (Unify q)  = Unify (substs s q)
    substs s (All e b)  = All (substs s e) (bind x (substs s p))
                              where (x, p) = unsafeUnbind b

instance Pretty Problem where
    pretty (Unify q) = pretty q
    pretty (All e b) = lunbind b $ \ (x, p) -> do
        e'  <- pretty e
        x'  <- pretty x
        p'  <- pretty p
        return $ (text "∀") <+> parens (x' <+> colon <+> e') <+> text " . " <+> p'


allProb :: Nom -> Type -> Problem -> Problem
allProb x _T p = All (P _T) (bind x p)

allTwinsProb :: Nom -> Type -> Type -> Problem -> Problem
allTwinsProb x _S _T p = All (Twins _S _T) (bind x p)

wrapProb :: [(Nom, Param)] -> Problem -> Problem
wrapProb []               p = p
wrapProb ((x, e) : _Gam)  p = All e (bind x (wrapProb _Gam p))



newtype ProbId = ProbId {probIdToName :: Nom}
  deriving (Eq, Show, Pretty, Generic)

instance Alpha ProbId
instance Subst VAL ProbId



data ProblemState =
  Blocked
  | Active
  | Pending [ProbId]
  | Solved
  | Failed Err
  | FailPending ProbId
  | Ignored
  deriving (Eq, Show, Generic)

instance Alpha ProblemState
instance Subst VAL ProblemState
instance Alpha IsCF
instance Alpha CreationInfo
instance Subst VAL IsCF
instance Subst VAL CreationInfo


instance Pretty ProblemState where
    pretty Blocked       = return $ text "BLOCKED"
    pretty Active        = return $ text "ACTIVE"
    pretty (Pending xs)  = return $ text $ "PENDING " ++ show xs
    pretty Solved        = return $ text "SOLVED"
    pretty Ignored        = return $ text "CF IGNORED"
    pretty (Failed e)    = return $ text $ "FAILED: " ++ e
    pretty (FailPending pid)    = return $ text $ "CF IF " ++ show pid ++ " FAILS: "

data IsCF = Factual | CounterFactual
  deriving (Eq, Ord, Show, Generic)

data Entry  =  E Nom Type Dec EqnInfo
            |  Prob ProbId Problem ProblemState
  deriving (Show, Generic)

probInfo :: Problem -> EqnInfo
probInfo (Unify (EQN _ _ _ _ info)) = info
probInfo (All params bnd) =
  let
    (_, innerProb) = unsafeUnbind bnd
  in
    probInfo innerProb


entryInfo :: Entry -> EqnInfo
entryInfo (E _ _ _ info) = info
entryInfo (Prob _ prob _) = probInfo prob
  where
    probInfo :: Problem -> EqnInfo
    probInfo (Unify (EQN _ _ _ _ info)) = info
    probInfo (All params bnd) =
      let
        (_, innerProb) = unsafeUnbind bnd
      in
        probInfo innerProb

instance Alpha Entry
instance Subst VAL Entry

instance Occurs Entry where
    occurrence xs (E _ _T d _)    = max (occurrence xs _T) (occurrence xs d)
    occurrence xs (Prob _ p _)  = occurrence xs p
    frees isMeta (E _ _T d _)     = union (frees isMeta _T) (frees isMeta d)
    frees isMeta (Prob _ p _)   = frees isMeta p

instance Pretty Entry where
    pretty (E x _T HOLE _)  = (between (text "? :")) <$> (pretty x) <*> (pretty _T)
    pretty (E x _T (DEFN d) _)  = (\ d' -> between (text ":=" <+> d' <+> text ":")) <$>
                                   (prettyAt PiSize d) <*> (pretty x) <*> (prettyAt PiSize _T)
    pretty (Prob x p s) =  (between (text "<=")) <$> ( (between (text "?? :")) <$> (pretty x) <*> (pretty p) ) <*> (pretty s)


instance Pretty Subs where
  pretty x = return $ text $ show $ Map.map pp x

data SimultSub = SimultSub Nom [(Nom, VAL, VAL)]
  deriving (Eq, Show, Generic)

splitSSS :: SimultSub -> (SubsList, SubsList)
splitSSS (SimultSub _ sss) =
  let
    (s1, s2, s3) = unzip3 sss
  in
    (zip s1 s2, zip s1 s3)


--We need to be able to store simultaneous substs in our right context
data RSubs =
  RSubs Subs
  | RSubImmediate ProbId Subs
  | RSimultSub SimultSub
  deriving (Eq, Show, Generic)

instance Pretty RSubs where
  pretty = return . text . show

type ContextL  = Bwd Entry
type ContextR  = [Either RSubs Entry]
type Context   = (ContextL, ContextR, ProbId, TypeGraph, BadEdges)

type VarEntry   = (Nom, Type)
type HoleEntry  = (Nom, Type)

data Param = P Type | Twins Type Type
   deriving (Show, Generic)

instance Alpha Param

instance Subst VAL Param

instance Occurs Param where
    occurrence xs (P _T)         = occurrence xs _T
    occurrence xs (Twins _S _T)  = max (occurrence xs _S) (occurrence xs _T)
    frees isMeta (P _T)          = frees isMeta _T
    frees isMeta (Twins _S _T)   = frees isMeta _S `union` frees isMeta _T

instance Pretty Param where
    pretty (P _T)         = pretty _T
    pretty (Twins _S _T)  =  (between (text "&")) <$> (pretty _S) <*> (pretty _T)


type Params  = [(Nom, Param)]

instance Pretty Context where
    pretty (cl, cr, _, _, _) =  pair <$>  (prettyEntries (trail cl)) <*>
                               ( vcat <$> (mapM f cr) )
      where
        pair cl' cr' = cl' $+$ text "*" $+$ cr'
        f (Left (RSubs ns)) = prettySubs ns
        f (Right e) = pretty e

prettyEntries :: (Applicative m, LFresh m, MonadReader Size m) => [Entry] -> m Doc
prettyEntries xs =  vcat <$> (mapM pretty xs)

prettySubs :: (Applicative m, LFresh m, MonadReader Size m) => Subs -> m Doc
prettySubs ns = (brackets . commaSep) <$> flip mapM (Map.toList ns)
                    (\ (x, v) -> ( (between (text "|->")) <$> (pretty x) <*> (pretty v) ))

prettyDeps :: (Applicative m, LFresh m, MonadReader Size m) => [(Nom, Type)] -> m Doc
prettyDeps ns = (brackets . commaSep) <$> flip mapM (ns)
                    (\ (x, _T) -> ( (between (text ":")) <$> (pretty x) <*> (pretty _T) ))

prettyDefns :: (Applicative m, LFresh m, MonadReader Size m) => [(Nom, Type, VAL)] -> m Doc
prettyDefns ns = (brackets . commaSep) <$> flip mapM ns
                    (\ (x, _T, v) -> ( f <$> (pretty x) <*> (pretty _T) <*> (pretty v) ))
   where f x' _T' v' = x' <+> text ":=" <+> v' <+> text ":" <+> _T'

prettyParams :: (Applicative m, LFresh m, MonadReader Size m) => Params -> m Doc
prettyParams xs = vcat <$> flip mapM xs
                     (\ (x, p) -> ( (between colon) <$> (pretty x) <*> (pretty p) ) )



type Err = (String)

newtype Contextual a = Contextual { unContextual ::
    ReaderT Params (ExceptT Err (FreshMT (StateT Context Identity))) a }
  deriving (Functor, Applicative, Monad,
                Fresh, MonadError Err,
                MonadState Context, MonadReader Params,
                MonadPlus, Alternative)


instance CM.HasTG Contextual ConstraintInfo where
  withTypeGraphM f = do
    ourGraph <- getGraph
    (ret, newGraph) <- f ourGraph
    setGraph newGraph
    return ret

instance Basic.HasBasic Contextual ConstraintInfo where

instance Writer.MonadWriter LogEntries Contextual where
  tell entries = --trace ("LOG " ++ show entries) $
    return ()
  listen = error "Contextual writer listen"
  pass = error "Contextual writer pass"

ctrace :: String -> Contextual ()
ctrace s = do
    cx    <- get
    _Gam  <- ask
    --trace (s ++ "\n" ++ pp cx ++ "\n---\n" ++ ppWith prettyParams _Gam)
    (return ()) >>= \ () -> return ()

runContextual :: Context -> Contextual a -> (Either Err a, Context)
runContextual cx =
   runIdentity . flip runStateT cx . runFreshMT . runExceptT . flip runReaderT [] . unContextual

modifyL :: (ContextL -> ContextL) -> Contextual ()
modifyL f = modify (\ (x, y, pid, gr, s) -> (f x, y, pid, gr, s))

modifyLM :: (ContextL -> Contextual ContextL) -> Contextual ()
modifyLM f = do
  (x, y, pid, gr, s) <- get
  fx <- f x
  put (fx, y, pid, gr, s)

modifyR :: (ContextR -> ContextR) -> Contextual ()
modifyR f = modify (\ (x, y, pid, gr, s) -> (x, f y, pid, gr, s))

pushL :: Entry -> Contextual ()
-- pushL e@((E alpha _ HOLE _)) | (show alpha) == "α_3_19__16" = trace ("pushL " ++ pp e) $ do
--   cl <- getL
--   cr <- getR
--   let
--     containsL e' = case e' of
--       (E a2 _ (DEFN _) _) -> alpha == a2
--       _ -> False
--     containsR e' = case e' of
--       (Right (E a2 _ (DEFN _) _)) -> alpha == a2
--       _ -> False
--   case (filter containsL cl, filter containsR cr) of
--     ([],[]) -> modifyL (:< e)
--     _ -> error "pushL 16"
pushL e = --trace ("Push left " ++ prettyString e) $
  modifyL (:< e)


pushR :: Either Subs Entry -> Contextual ()
--pushR (Right (E alpha _ HOLE _)) | (show alpha) == "α_3_19__16" = error "pushR 16"
pushR (Left s)   = --trace ("Push subs " ++ show s) $
  pushSubs s
pushR (Right e)  = --trace ("Push right " ++ prettyString e) $
  modifyR (Right e :)

pushSSS :: SimultSub -> Contextual ()
pushSSS sss@(SimultSub _ s)   = --trace ("Push subs " ++ show s) $
  case s of
    [] -> return ()
    _ ->
      modifyR (Left (RSimultSub sss) : )

pushImmediate :: ProbId -> Subs -> Contextual ()
pushImmediate pid theta   = --trace ("Push subs " ++ show s) $
  modifyR (Left (RSubImmediate pid theta) : )


setProblem :: ProbId -> Contextual ()
setProblem pid = modify (\ (x, y, _, z, s) -> (x, y, pid, z, s))

setGraph :: TypeGraph -> Contextual ()
setGraph g = modify (\ (x, y, z, _, s) -> (x, y, z, g, s))

setMsg :: BadEdges -> Contextual ()
setMsg s = modify (\(x,y,z,g,_) -> (x,y,z,g,s))

pushSubs :: Subs -> Contextual ()
pushSubs n   =
  if Map.null n then
    return ()
  else
    modifyR (\ cr -> if null cr then [] else Left (RSubs n) : cr)

popL :: Contextual Entry
popL = do
    cx <- getL
    case cx of
        (cx' :< e)  -> putL cx' >> return e
        B0          -> throwError "popL ran out of context"
        _ -> undefined

popR :: Contextual (Maybe (Either RSubs Entry))
popR = do
    cx <- getR
    case cx of
        (x  : cx')  -> putR cx' >> return (Just x)
        []          -> return Nothing

getL :: MonadState Context m => m ContextL
getL = gets (\(x,_,_,_,_) -> x)

getR :: Contextual ContextR
getR = gets (\(_,x,_,_,_) -> x)

getGraph :: Contextual (TypeGraph)
getGraph = gets (\(_,_,_,g,_) -> g)

putL :: ContextL -> Contextual ()
putL x = modifyL (const x)

putR :: ContextR -> Contextual ()
putR x = modifyR (const x)


inScope :: MonadReader Params m => Nom -> Param -> m a -> m a
inScope x p = local (++ [(x, p)])

localParams :: (Params -> Params) -> Contextual a -> Contextual a
localParams f = local f

lookupVar :: Nom -> Twin -> Contextual Type
lookupVar x w = do
  vars <- ask
  look vars vars
  where
    look vars [] = error $ "lookupVar: missing " ++ show x ++ "\nin env " ++ show vars
    look vars  ((y, e) : _) | x == y =
      case (e, w) of
        (P _T,         Only)   -> return _T
        (Twins _S _T,  TwinL)  -> return _S
        (Twins _S _T,  TwinR)  -> return _T
        _                      -> error $ "lookupVar: evil twin | " ++ show y ++ " | " ++ show e ++ " | " ++ show w
    look vars (_ : _Gam)                      = look vars _Gam

lookupMeta :: Nom -> Contextual Type
lookupMeta x = look =<< getL
  where
    --look :: Monad m => ContextL -> m Type
    look B0 = error $ "lookupMeta: missing " ++ show x
    look (cx  :< E y t _ _)  | x == y     = return t
                           | otherwise  = look cx
    look (cx  :< Prob _ _ _) = look cx
    look _ = undefined

metaSubs :: MonadState Context m => m Subs
metaSubs = do
  leftContext <- getL
  let pairList = Maybe.catMaybes $ map maybeSub leftContext
  --trace ("MetaSubs " ++ show pairList) $
  return $ Map.fromList $ pairList


maybeSub :: Entry -> Maybe (Nom, VAL)
maybeSub (E y _ (DEFN val) _) = Just (y,val)
maybeSub _ = Nothing

--We only consider unsolved from the first elements of split defns
--TODO is this right? What about fst nested in second?
getUnsolvedAndSolved :: [Entry] -> ([(Nom, Region, Maybe VAL)], Subs)
getUnsolvedAndSolved [] = return Map.empty
getUnsolvedAndSolved (entry : rest) =
  let
    (uns, solved) = getUnsolvedAndSolved rest
  in
    case entry of
      E y _ (DEFN valNotFlat) info | isCF info == Factual ->
        let
          val = unsafeFlatten valNotFlat
        in trace ("getUnsolved flattened to " ++ pp val) $ case fmvs val of
          [] -> (uns, Map.insert y val solved)
          _ -> trace ("Unsolved meta in" ++ pp val) $ ((y, infoRegion info, Just val) : uns, solved)
      E y _ HOLE info | isCF info == Factual ->
        trace ("Unsolved HOLE " ++ show y) $ ((y, infoRegion info, Nothing) : uns, solved)
      _ -> (uns, solved)

metaValue :: MonadState Context m => Nom -> m VAL
metaValue x = look =<< getL
  where
    look :: Monad m => ContextL -> m Type
    look B0 = fail $ "metaValue: missing " ++ show x
    look (cx  :< E y _ (DEFN val) _)  | x == y     = return val
                           | otherwise  = look cx
    look (cx  :< Prob _ _ _) = look cx
    look (cx  :< E y _ HOLE _)  | x == y     = return $ meta x
                           | otherwise  = look cx
    look _ = undefined



addEqn :: (Fresh m) => info -> Equation -> TG.StandardTypeGraph info -> m (TG.StandardTypeGraph info)
--Avoid polluting our graph with a bunch of reflexive equations
addEqn info eqn@(EQN _ v1 _ v2 _) stg | v1 == v2 = return stg
addEqn info eqn@(EQN _ v1 _ v2 _) stg = --trace ("Adding equation to graph " ++ show eqn) $
    TG.addEqn info (v1, v2) stg

recordEqn :: ConstraintType -> Equation -> Contextual ()
recordEqn ctype eqn@(EQN _ _ _ _ eqinfo) = do
  gCurrent <- getGraph
  let cinfo = ConstraintInfo ctype eqinfo
  newG <- addEqn cinfo eqn gCurrent
  setGraph newG

recordProblem :: ConstraintType -> ProbId -> Problem -> Contextual ()
recordProblem info (ProbId pid) prob = recordProblem' prob 0
  where
    recordProblem' (Unify q) _ = recordEqn info q
    recordProblem' (All tp bnd) i = do
      (nm, prob) <- unbind bnd
      --Create a unique (but not fresh) name for our quanitified variable
      --in the scope of this problem
      let newVarBase = name2String pid ++ "_quant"
          newVar = makeName newVarBase i
          newProb = substs [(nm, var newVar)] prob
      recordProblem' newProb (i+1)

-- --TODO do we need this? record problem substs?
-- recordEntry :: Entry -> Contextual ()
-- recordEntry (E nm tp HOLE) = return ()
-- recordEntry (E nm tp (DEFN dec)) = recordEqn _ (EQN tp (meta nm) tp dec)
-- recordEntry (Prob pid prob st) = recordProblem pid prob --TODO look at state?

--After we substitute new values, we record the equalities between the subsituted values
--This lets us get eliminate Function Application edges in our graph
recordEntrySub :: Entry -> Entry -> Contextual ()
recordEntrySub (E nm1 tp1 HOLE _) (E nm2 tp2 HOLE _) = return () --TODO will ever change?
recordEntrySub (E alpha tp1 (DEFN dec1) _) (E _ tp2 (DEFN dec2) info) =
  recordEqn (DefnUpdate alpha) (EQN tp1 dec1 tp2 dec2 info)
recordEntrySub (Prob pid prob _) (Prob _ prob2 _) =
  recordProblemSub pid prob prob2

--Decompose the problems in parallel, creating matching
--names for their quantified variables
recordProblemSub :: ProbId -> Problem -> Problem -> Contextual ()
recordProblemSub (ProbId pid) prob1 prob2 = helper' prob1 prob2 0
  where
    helper' (Unify (EQN t1 v1 t2 v2 _)) (Unify (EQN t1' v1' t2' v2' creator)) _ = do
      recordEqn (ProbUpdate $ ProbId pid) $ EQN t1 v1 t1' v1' creator
      recordEqn (ProbUpdate $ ProbId pid) $ EQN t2 v2 t2' v2' creator
    helper' (All tp bnd1) (All _ bnd2) i = do
      (nm1, prob1) <- unbind bnd1
      (nm2, prob2) <- unbind bnd2
      --Create a unique (but not fresh) name for our quanitified variable
      --in the scope of this problem
      let newVarBase = name2String pid ++ "_quant"
          newVar = makeName newVarBase i
          newProb1 = substs [(nm1, var newVar)] prob1
          newProb2 = substs [(nm2, var newVar)] prob2
      helper' newProb1 newProb2 (i+1)


flattenEquation :: (Fresh m) => Equation -> m Equation
flattenEquation (EQN _T1 t1 _T2 t2 info) =
  EQN <$> flattenChoice _T1 <*> flattenChoice t1
    <*> flattenChoice _T2 <*> flattenChoice t2 <*> return info
