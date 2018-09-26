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

module PatternUnify.Context
  ( module PatternUnify.ConstraintInfo
  , module PatternUnify.Context) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import qualified Control.Monad.Writer as Writer

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set

--import Debug.Trace (trace)
import GHC.Generics

import Unbound.Generics.LocallyNameless hiding (join, restrict)
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
--import Unbound.LocallyNameless.Types (GenBind(..))

import PatternUnify.Kit
import PatternUnify.Tm

import PatternUnify.SolverConfig

--import Debug.Trace (trace)

import Data.List (union)

import qualified Top.Implementation.TypeGraph.Standard as TG

import qualified Top.Interface.Basic as Basic

import qualified Top.Implementation.TypeGraph.ClassMonadic as CM

import qualified Top.Implementation.TypeGraph.ApplyHeuristics as Heur

import Top.Solver (LogEntries)

import PatternUnify.Tm (Region)
import Text.Parsec (SourcePos)

import qualified Top.Interface.Substitution as Sub
import qualified Top.Types.Substitution as TSub

import PatternUnify.ConstraintInfo

import qualified Top.Util.Empty as Empty

import Data.Foldable (foldrM)

type BadEdges = [Heur.ErrorInfo ConstraintInfo]

type TypeGraph = TG.StandardTypeGraph

data Dec = HOLE | DEFN VAL
  deriving (Show, Generic)

instance Alpha Dec
instance Subst VAL Dec

instance Occurs Dec where
    occurrence _  HOLE      = Nothing
    occurrence xs (DEFN t)  = occurrence xs t
    frees _       HOLE      = []
    frees isMeta  (DEFN t)  = frees isMeta t




data Equation = EQN Type VAL Type VAL EqnInfo
  deriving (Show, Generic)

instance Alpha Equation

instance Subst VAL Equation where


instance Occurs Equation where
    occurrence xs (EQN _S s _T t _) = occurrence xs [_S, s, _T, t]
    frees isMeta (EQN _S s _T t _) = frees isMeta [_S, s, _T, t]

instance Pretty Equation where
  pretty (EQN _S s _T t _) =  f <$> (pretty _S) <*> (pretty s) <*> (pretty _T) <*> (prettyVal t)
      where f _S' s' _T' t' = parens (s' <+> colon <+> _S') <+>
                                  text "===" <+> parens (t' <+> colon <+> _T')
            prettyVal :: (Applicative m, LFresh m, MonadReader Size m) => VAL -> m Doc
            prettyVal v = pretty v


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



instance Pretty ProblemState where
    pretty Blocked       = return $ text "BLOCKED"
    pretty Active        = return $ text "ACTIVE"
    pretty (Pending xs)  = return $ text $ "PENDING " ++ show xs
    pretty Solved        = return $ text "SOLVED"
    pretty Ignored        = return $ text "CF IGNORED"
    pretty (Failed e)    = return $ text $ "FAILED: " ++ e
    pretty (FailPending pid)    = return $ text $ "CF IF " ++ show pid ++ " FAILS: "


data Entry  =  E Nom Type Dec EqnInfo
            |  Prob ProbId Problem ProblemState [Entry]
  deriving (Show, Generic)

makeFailPend :: ProbId -> Entry -> Entry
makeFailPend n (Prob pid p _ failWaits) = Prob pid p (FailPending n) failWaits
makeFailPend _ e = e

addFailWaits :: [Entry] -> Entry -> Entry
addFailWaits newWaits (Prob pid p st waits) = Prob pid p st $ waits ++ newWaits
addFailWaits _ e = e

probInfo :: Problem -> EqnInfo
probInfo (Unify (EQN _ _ _ _ info)) = info
probInfo (All params bnd) =
  let
    (_, innerProb) = unsafeUnbind bnd
  in
    probInfo innerProb

-- modifyProbInfo :: (EqnInfo -> EqnInfo) -> Problem -> Contextual Problem
-- modifyProbInfo (All params bnd) = _



entryInfo :: Entry -> EqnInfo
entryInfo (E _ _ _ info ) = info
entryInfo (Prob _ prob _ _) = probInfo prob
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
    occurrence xs (E _ _T d _ )    = max (occurrence xs _T) (occurrence xs d)
    occurrence xs (Prob _ p _ _)  = occurrence xs p
    frees isMeta (E _ _T d _ )     = union (frees isMeta _T) (frees isMeta d)
    frees isMeta (Prob _ p _ _)   = frees isMeta p

instance Pretty Entry where
    pretty (E x _T HOLE _ )  = (between (text "? :")) <$> (pretty x) <*> (pretty _T )
    pretty (E x _T (DEFN d) _ )  = (\ d' -> between (text ":=" <+> d' <+> text ":")) <$>
                                   (prettyAt PiSize d) <*> (pretty x) <*> (prettyAt PiSize _T)
    pretty (Prob x p s _) =  (between (text "<=")) <$> ( (between (text "?? :")) <$> (pretty x) <*> (pretty p) ) <*> (pretty s)


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
--  | RSimultSub SimultSub
  deriving (Eq, Show, Generic)

instance Pretty RSubs where
  pretty = return . text . show

type ContextL  = Bwd Entry
type ContextR  = [Either RSubs Entry]
data Context   = Context
  { contextL :: ContextL
  , contextR :: ContextR
  , contextPid :: ProbId
  , contextGraph :: TypeGraph
  , contextBadEdges :: BadEdges
  , contextNomPids :: Set.Set (Either Nom ProbId)
  , contextSolverConfig :: SolverConfig
  , contextVarLabels :: Map.Map Nom (Nom, CFChoices)
  , contextQualificationsOf :: Map.Map Nom [Nom]
  }

lookupLabel :: Nom -> Contextual (Nom, CFChoices)
lookupLabel n = do
  m <- gets contextVarLabels
  return $ Maybe.fromMaybe (n,Set.empty) $ Map.lookup n m

qualsOf :: Nom -> Contextual [Nom]
qualsOf n = do
  m <- gets contextQualificationsOf
  return $  Maybe.fromMaybe [] $ Map.lookup n m

--To get the labelled meta for a path, first we find if it exists
--If it does, we just return it
--Otherwise, we generate a fresh variable on the right

labelledMetaFor :: Nom -> CFChoices -> Contextual Nom
labelledMetaFor n ch = do
  (topN, quals) <- lookupLabel n
  quals <- qualsOf topN
  qualLabels <- (zip quals) <$> forM quals lookupLabel
  let potentialQuals = filter (\(_,(nPotential,chPotential)) -> chPotential == ch && nPotential == topN) qualLabels
  case potentialQuals of
    [] -> do
      retN <- fresh n
      modify (\c -> 
        let mp = contextVarLabels c 
            quals = contextQualificationsOf c
            --TODO record in constraint graph
            topEntry = Maybe.fromMaybe [] $ Map.lookup topN quals 
            newQuals = Map.insert topN (retN : topEntry) quals    
        in  c {contextVarLabels = Map.insert retN (topN, ch) mp, contextQualificationsOf = newQuals })
      return n
    [(retN, _)] -> return retN 
    _ -> error $ "Multiple quals of " ++ name2String topN ++ " matching label " ++ show ch ++ " LIST: " ++ show potentialQuals

data ChoiceLabel = ChoiceL {labelCh :: ChoiceId} | ChoiceR {labelCh :: ChoiceId}
  deriving (Eq, Ord, Show)

isRight (ChoiceR _) = True
isRight _ = False

cfChoices :: [ChoiceLabel] -> CFChoices
cfChoices cls = Set.fromList $ map labelCh $ filter isRight cls

type CFChoices = Set.Set ChoiceId

initContext :: Context
initContext = Context B0 [] (error "initial problem ID") Empty.empty [] Set.empty (SolverConfig True True True) Map.empty Map.empty

type VarEntry   = (Nom, Type)
type HoleEntry  = (Nom, Type)

prettyList l = List.intercalate "\n" $ map pp l



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
    pretty c =  pair <$>  (prettyEntries (trail $ contextL c)) <*>
                               ( vcat <$> (mapM f $ contextR c) )
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

instance Sub.HasSubst Contextual ConstraintInfo where

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
modifyL f = modify (\ c -> c {contextL = f (contextL c)})

modifyLM :: (ContextL -> Contextual ContextL) -> Contextual ()
modifyLM f = do
  c <- get
  fx <- f (contextL c)
  put (c {contextL = fx})

modifyR :: (ContextR -> ContextR) -> Contextual ()
modifyR f = modify (\c -> c {contextR = f (contextR c)})

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

-- pushSSS :: SimultSub -> Contextual ()
-- pushSSS sss@(SimultSub _ s)   = --trace ("Push subs " ++ show s) $
--   case s of
--     [] -> return ()
--     _ ->
--       modifyR (Left (RSimultSub sss) : )

pushImmediate :: ProbId -> Subs -> Contextual ()
pushImmediate pid theta   = --trace ("Push subs " ++ show s) $
  modifyR (Left (RSubImmediate pid theta) : )


markDefInGraph :: Nom -> Contextual ()
markDefInGraph alpha = modify (\c -> let set = (contextNomPids c) in c {contextNomPids =  Set.insert (Left alpha) set})

markProblemInGraph :: ProbId -> Contextual ()
markProblemInGraph newPid = modify $
  \ c -> let set = contextNomPids c in
    c {contextNomPids = Set.insert (Right newPid) set}

probAlreadyRecorded :: ProbId -> Contextual Bool
probAlreadyRecorded newPid = do
  c <- get
  return $ Right newPid `Set.member` (contextNomPids c)

defAlreadyRecorded :: Nom -> Contextual Bool
defAlreadyRecorded alpha = do
  c <- get
  return $ Left alpha `Set.member` (contextNomPids c)

setProblem :: ProbId -> Contextual ()
setProblem pid = modify (\ c -> c {contextPid = pid} :: Context)

setGraph :: TypeGraph -> Contextual ()
setGraph g = modify (\ c -> c {contextGraph = g})

setMsg :: BadEdges -> Contextual ()
setMsg s = modify (\c -> c {contextBadEdges = s})

pushSubs :: Subs -> Contextual ()
pushSubs n   =
  if Map.null n then
    return ()
  else
    modifyR (\ cr -> if null cr then [] else Left (RSubs n) : cr)

mpopL :: Contextual (Maybe Entry)
mpopL = do
    cx <- getL
    case cx of
        --((E x _ _ _) : _) | (show x == "β_6_25") && (trace ("popL β_6_25 ") False) -> error "popL case"
        (cx' :< e)  -> putL cx' >> return (Just e)
        B0          -> return Nothing
        _ -> undefined

popL :: Contextual Entry
popL = do
    cx <- getL
    case cx of
        --((E x _ _ _) : _) | (show x == "β_6_25") && (trace ("popL β_6_25 ") False) -> error "popL case"
        (cx' :< e)  -> putL cx' >> return e
        B0          -> error "popL ran out of context"
        _ -> undefined

popR :: Contextual (Maybe (Either RSubs Entry))
popR = do
    cx <- getR
    case cx of
        --(Right (E x _ _ _) : _) | (show x == "β_6_25") && (trace ("popR β_6_25 ") False) -> error "popR case"
        (x  : cx')  -> putR cx' >> return (Just x)
        []          -> return Nothing

getConfig :: Contextual SolverConfig
getConfig = gets contextSolverConfig

getL :: MonadState Context m => m ContextL
getL = gets contextL

getR :: Contextual ContextR
getR = gets contextR

getGraph :: Contextual (TypeGraph)
getGraph = gets contextGraph

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
lookupMeta x = do
  cl <- getL
  cr <- getR
  --look :: Monad m => ContextL -> m Type
  let
    look B0 = error $ "lookupMeta: missing " ++ show x ++ "\nCL:\n" ++ List.intercalate "\n" (map pp cl) ++ "\nCR\n" ++ List.intercalate "\n" (map pp cr)
    look (cx  :< E y t _ _ )  | x == y     = return t
                           | otherwise  = look cx
    look (cx  :< Prob _ _ _ _) = look cx
    look _ = undefined
  look cl
  where


metaSubs :: MonadState Context m => m Subs
metaSubs = do
  leftContext <- getL
  let pairList = Maybe.catMaybes $ map maybeSub leftContext
  --trace ("MetaSubs " ++ show pairList) $
  return $ Map.fromList $ pairList


maybeSub :: Entry -> Maybe (Nom, VAL)
maybeSub (E y _ (DEFN val) _ ) = Just (y,val)
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
      E y _ (DEFN valNotFlat) info  | isCF info == Factual ->
        let
          val = unsafeFlatten valNotFlat
        in case fmvs val of
          [] -> (uns, Map.insert y val solved)
          _ -> --trace ("Unsolved meta in" ++ pp val) $
            ((y, infoRegion info, Just val) : uns, solved)
      E y _ HOLE info  | isCF info == Factual ->
        --trace ("Unsolved HOLE " ++ show y) $
        ((y, infoRegion info, Nothing) : uns, solved)
      _ -> (uns, solved)

metaValue :: MonadState Context m => Nom -> m VAL
metaValue x = look =<< getL
  where 
    look :: Monad m => ContextL -> m Type
    look B0 = fail $ "metaValue: missing " ++ show x
    look (cx  :< E y _ (DEFN val) _ )  | x == y     = return val
                           | otherwise  = look cx
    look (cx  :< Prob _ _ _ _) = look cx
    look (cx  :< E y _ HOLE _)  | x == y     = return $ meta x
                           | otherwise  = look cx
    look _ = undefined



addEqn :: (Fresh m) => ConstraintInfo -> Equation -> TG.StandardTypeGraph -> m (TG.StandardTypeGraph)
--Avoid polluting our graph with a bunch of reflexive equations
addEqn info eqn@(EQN _ v1 _ v2 _) stg | v1 == v2 = return stg
addEqn info eqn@(EQN _ v1 _ v2 _) stg = --trace ("Adding equation to graph " ++ show eqn) $
    TG.addEqn info (v1, v2) stg

recordEqn :: ConstraintType -> Equation -> Contextual ()
recordEqn ctype eqn@(EQN _T sc _ tc eqinfo) = do
  s <- flattenChoice sc
  t <- flattenChoice tc
  gCurrent <- getGraph
  let cinfo = ConstraintInfo ctype eqinfo (s,t) _T Nothing
  newG <- addEqn cinfo eqn gCurrent
  setGraph newG

recordProblem :: ConstraintType -> ProbId -> Problem -> Contextual ()
recordProblem info (ProbId pid) prob = recordProblem' prob 0
  where
    recordProblem' (Unify q) _ = recordEqn info q
    recordProblem' (All param bnd) i = do
      (nm, prob) <- unbind bnd
      --Create a unique (but not fresh) name for our quanitified variable
      --in the scope of this problem
      let newVarBase = name2String pid ++ "_quant"
          newVar = makeName newVarBase i
          newProb = substs [(nm, var newVar)] prob
      recordProblem' newProb (i+1)
      CM.recordVar newVar param

recordChoice :: Type -> Nom -> VAL -> VAL -> EqnInfo -> Contextual ()
recordChoice  _T x vsingle freshVar info = --trace ("RECORDING choice " ++ show x ++ " to " ++ show freshVar) $
 do
  constrNom <- fresh $ s2n "chInter"
  let constrMeta = meta constrNom
  --Record our choice in our graph
  recordEqn (ChoiceEdge LeftChoice x (vsingle, freshVar)) (EQN _T (meta x) _T constrMeta info)
  recordUpdate info _T (x, constrMeta)
  recordEqn (ChoiceEdge RightChoice x (vsingle, freshVar)) (EQN _T freshVar _T constrMeta info)
  recordUpdate info _T (constrNom, freshVar)



recordDefn :: Nom -> Type -> VAL -> EqnInfo -> Contextual ()
recordDefn alpha _T t info = do
  --Don't record duplicate equations for implied equalities
  unless (isImpliedEquality info) $ recordEqn (DefineMeta alpha) (EQN _T (meta alpha) _T t info)
  recordUpdate info _T (alpha, t)
  markDefInGraph alpha

recordEntry :: Entry -> Contextual ()
recordEntry (E alpha _T HOLE info) = return ()
recordEntry (E alpha _T (DEFN t) info) = do
  b <- defAlreadyRecorded alpha
  unless (b ) $ recordDefn alpha _T t info
recordEntry (Prob pid prob _ _) = do
  b <- probAlreadyRecorded pid
  let
    edgeType =
      case creationInfo (probInfo prob) of
        Initial -> InitConstr pid
        _ -> DerivedEqn pid
  unless b $ recordProblem edgeType pid prob
  markProblemInGraph pid

-- --TODO do we need this? record problem substs?
-- recordEntry :: Entry -> Contextual ()
-- recordEntry (E nm tp HOLE) = return ()
-- recordEntry (E nm tp (DEFN dec)) = recordEqn _ (EQN tp (meta nm) tp dec)
-- recordEntry (Prob pid prob st) = recordProblem pid prob --TODO look at state?


recordUpdate :: EqnInfo -> Type -> (Nom, VAL) -> Contextual ()
recordUpdate info _T sub = do
    gCurrent <- getGraph
    newG <- TG.processUpdate (\ pr -> ConstraintInfo (MetaUpdate sub) info pr _T Nothing) sub gCurrent
    setGraph newG


--After we substitute new values, we record the equalities between the subsituted values
--This lets us get eliminate Function Application edges in our graph
-- recordEntrySub :: Entry -> Entry -> Contextual ()
-- recordEntrySub (E nm1 tp1 HOLE _) (E nm2 tp2 HOLE _) = return () --TODO will ever change?
-- recordEntrySub (E alpha tp1 (DEFN dec1) _) (E _ tp2 (DEFN dec2) info) =
--   recordEqn (DefnUpdate alpha) (EQN tp1 dec1 tp2 dec2 info)
-- recordEntrySub (Prob pid prob _ _) (Prob _ prob2 _ _) =
--   recordProblemSub pid prob prob2

-- --Decompose the problems in parallel, creating matching
-- --names for their quantified variables
-- recordProblemSub :: ProbId -> Problem -> Problem -> Contextual ()
-- recordProblemSub (ProbId pid) prob1 prob2 = helper' prob1 prob2 0
--   where
--     helper' (Unify (EQN t1 v1 t2 v2 _)) (Unify (EQN t1' v1' t2' v2' info)) _ = do
--         recordEqn (ProbUpdate $ ProbId pid) $ EQN t1' v1 t2' v2' (info {creationInfo = CreatedBy $ ProbId pid})
--       --recordEqn (ProbUpdate $ ProbId pid) $ EQN t1 v1 t1' v1' creator
--       --recordEqn (ProbUpdate $ ProbId pid) $ EQN t2 v2 t2' v2' creator
--     helper' (All tp bnd1) (All _ bnd2) i = do
--       (nm1, prob1) <- unbind bnd1
--       (nm2, prob2) <- unbind bnd2
--       --Create a unique (but not fresh) name for our quanitified variable
--       --in the scope of this problem
--       let newVarBase = name2String pid ++ "_quant"
--           newVar = makeName newVarBase i
--           newProb1 = substs [(nm1, var newVar)] prob1
--           newProb2 = substs [(nm2, var newVar)] prob2
--       helper' newProb1 newProb2 (i+1)


flattenEquation :: (Fresh m) => Equation -> m Equation
flattenEquation (EQN _T1 t1 _T2 t2 info) =
  EQN <$> flattenChoice _T1 <*> flattenChoice t1
    <*> flattenChoice _T2 <*> flattenChoice t2 <*> return info

freshenChoice :: [ChoiceLabel] -> VAL -> Contextual VAL
freshenChoice c (L t) = do
  (var, body) <- unbind t
  newBody <- freshenChoice c body
  return $ L $ bind var newBody
freshenChoice c (N (Meta n) elims) = do--case for meta, check its path
  labelledMeta <- labelledMetaFor n $ cfChoices c
  N (Meta labelledMeta) <$> mapM (freshenChoiceElim c) elims
freshenChoice c (N v elims) =
  N v <$> mapM (freshenChoiceElim c) elims
freshenChoice c (C t1 t2) =
  C t1 <$> (mapM $ freshenChoice c) t2
freshenChoice c (VBot t) = return $ VBot t
freshenChoice c (VChoice cid cuid n t1 t2) = --Eliminate nested choices
  case [someChoice | someChoice <- c, labelCh someChoice == cid] of
    [] ->
      VChoice cid cuid n <$> freshenChoice ( (ChoiceL cid) : c) t1 <*> freshenChoice ( (ChoiceR cid) : c) t2
    [ChoiceL cid] -> freshenChoice c t1
    [ChoiceR cid] -> freshenChoice c t2

freshenChoiceElim :: [ChoiceLabel] -> Elim -> Contextual Elim
freshenChoiceElim c (Elim e1 e2) = Elim e1 <$> mapM (freshenChoice c)  e2
freshenChoiceElim c (EBot e) = return $ EBot e

fixSplitVars :: [ChoiceLabel] -> VAL -> Contextual VAL
fixSplitVars c (L t) = do
  (var, body) <- unbind t
  newBody <- fixSplitVars c body
  return $ L $ bind var newBody
fixSplitVars c (N (Meta n) elims) = do--case for meta, check its path
    qualsMap <- gets contextQualificationsOf
    let choiceList = map labelCh c
    let quals = Maybe.fromMaybe [] $ Map.lookup n qualsMap 
    qualVarsSets <-  (forM quals lookupLabel)
    let qualVars =  Set.toList $ Set.unions $ map snd qualVarsSets
    let notCovered  = [ch | (ch) <- qualVars, not (ch `List.elem` choiceList) ]
    let foldFun :: ChoiceId -> VAL -> Contextual VAL 
        foldFun ch soFar = do
          nNew <- fresh n
          newCUID <- freshCUID
          return $ VChoice ch newCUID n soFar (meta nNew) 
      
    newVar <- foldrM foldFun (meta n) notCovered
    newElims <- (mapM (fixSplitVarsElim c) elims)
    newVar %%% newElims
fixSplitVars c (N v elims) =
  N v <$> mapM (fixSplitVarsElim c) elims
fixSplitVars c (C t1 t2) =
  C t1 <$> (mapM $ fixSplitVars c) t2
fixSplitVars c (VBot t) = return $ VBot t
fixSplitVars c (VChoice cid cuid n t1 t2) = --Eliminate nested choices
  case [someChoice | someChoice <- c, labelCh someChoice == cid] of
    [] ->
      VChoice cid cuid n <$> fixSplitVars ( (ChoiceL cid) : c) t1 <*> fixSplitVars ( (ChoiceR cid) : c) t2
    [ChoiceL cid] -> fixSplitVars c t1
    [ChoiceR cid] -> fixSplitVars c t2

fixSplitVarsElim :: [ChoiceLabel] -> Elim -> Contextual Elim
fixSplitVarsElim c (Elim e1 e2) = Elim e1 <$> mapM (fixSplitVars c)  e2
fixSplitVarsElim c (EBot e) = return $ EBot e

fixChoices v = do
  v1 <- freshenChoice [] v
  v2 <- fixSplitVars [] v1
  return v2

hoist :: ChoiceId -> VAL -> Contextual VAL
hoist c v = do
  (v1, v2) <- splitOnChoice c v
  cuid <- freshCUID
  fixChoices $ VChoice c cuid (error "TODO what is this nom?") v1 v2

finalSub :: ContextL -> SubsList
finalSub = Maybe.mapMaybe getDef
  where
    getDef (E alpha _ (DEFN t) _ ) = Just (alpha, t)
    getDef _ = Nothing

--Check if a problem is just a trivial variable assignment, to avoid redundant edges

singleVarEntry :: Entry -> Contextual Bool
singleVarEntry (Prob _ prob _ _) = singleVarProb prob
singleVarEntry _ = return False

singleVarProb :: Problem -> Contextual Bool
singleVarProb (Unify (EQN _ (N (Meta alpha) []) _ _ _)) = return True
singleVarProb (Unify (EQN _ _ _ (N (Meta alpha) []) _)) = return True
singleVarProb (All _ p2) = do
  (x, p) <- unbind p2
  singleVarProb p
singleVarProb _ = return False
