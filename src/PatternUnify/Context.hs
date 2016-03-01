--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE GADTs, KindSignatures, TemplateHaskell, BangPatterns,
      FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
      UndecidableInstances, GeneralizedNewtypeDeriving,
      TypeSynonymInstances, ScopedTypeVariables, StandaloneDeriving, PatternSynonyms #-}

-- This module defines unification problems, metacontexts and operations
-- for working on them in the |Contextual| monad.

module PatternUnify.Context where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import Debug.Trace

import Unbound.LocallyNameless hiding (restrict, join)
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Unbound.LocallyNameless.Types (GenBind(..))

import PatternUnify.Kit
import PatternUnify.Tm


data Dec = HOLE | DEFN VAL
  deriving Show

instance Alpha Dec
instance Subst VAL Dec

instance Occurs Dec where
    occurrence _  HOLE      = Nothing
    occurrence xs (DEFN t)  = occurrence xs t
    frees _       HOLE      = emptyC
    frees isMeta  (DEFN t)  = frees isMeta t

data Equation = EQN Type VAL Type VAL
  deriving Show

instance Alpha Equation
instance Subst VAL Equation

instance Occurs Equation where
    occurrence xs (EQN _S s _T t) = occurrence xs [_S, s, _T, t]
    frees isMeta (EQN _S s _T t) = frees isMeta [_S, s, _T, t]

instance Pretty Equation where
  pretty (EQN _S s _T t) =  f <$> (pretty _S) <*> (pretty s) <*> (pretty _T) <*> (prettyVal t)
      where f _S' s' _T' t' = parens (s' <+> colon <+> _S') <+>
                                  text "===" <+> parens (t' <+> colon <+> _T')
            prettyVal :: (Applicative m, LFresh m, MonadReader Size m) => VAL -> m Doc
            prettyVal v = pretty v

data Problem  =  Unify Equation
              |  All Param (Bind Nom Problem)
  deriving Show

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
--


newtype ProbId = ProbId Nom
  deriving (Eq, Show, Pretty)

instance Alpha ProbId
instance Subst VAL ProbId



data ProblemState = Blocked | Active | Pending [ProbId] | Solved | Failed Err
  deriving (Eq, Show)

instance Alpha ProblemState
instance Subst VAL ProblemState

instance Pretty ProblemState where
    pretty Blocked       = return $ text "BLOCKED"
    pretty Active        = return $ text "ACTIVE"
    pretty (Pending xs)  = return $ text $ "PENDING " ++ show xs
    pretty Solved        = return $ text "SOLVED"
    pretty (Failed e)    = return $ text $ "FAILED: " ++ e


data Entry  =  E Nom Type Dec
            |  Prob ProbId Problem ProblemState
  deriving Show

instance Alpha Entry
instance Subst VAL Entry

instance Occurs Entry where
    occurrence xs (E _ _T d)    = max (occurrence xs _T) (occurrence xs d)
    occurrence xs (Prob _ p _)  = occurrence xs p
    frees isMeta (E _ _T d)     = union (frees isMeta _T) (frees isMeta d)
    frees isMeta (Prob _ p _)   = frees isMeta p

instance Pretty Entry where
    pretty (E x _T HOLE)  = (between (text "? :")) <$> (pretty x) <*> (pretty _T)
    pretty (E x _T (DEFN d))  = (\ d' -> between (text ":=" <+> d' <+> text ":")) <$>
                                   (prettyAt PiSize d) <*> (pretty x) <*> (prettyAt PiSize _T)
    pretty (Prob x p s) =  (between (text "<=")) <$> ( (between (text "?? :")) <$> (pretty x) <*> (pretty p) ) <*> (pretty s)



type ContextL  = Bwd Entry
type ContextR  = [Either Subs Entry]
type Context   = (ContextL, ContextR)

type VarEntry   = (Nom, Type)
type HoleEntry  = (Nom, Type)

data Param = P Type | Twins Type Type
   deriving Show

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
    pretty (cl, cr) =  pair <$>  (prettyEntries (trail cl)) <*>
                               ( vcat <$> (mapM f cr) )
      where
        pair cl' cr' = cl' $+$ text "*" $+$ cr'
        f (Left ns) = prettySubs ns
        f (Right e) = pretty e

prettyEntries :: (Applicative m, LFresh m, MonadReader Size m) => [Entry] -> m Doc
prettyEntries xs =  vcat <$> (mapM pretty xs)

prettySubs :: (Applicative m, LFresh m, MonadReader Size m) => Subs -> m Doc
prettySubs ns = (brackets . commaSep) <$> flip mapM ns
                    (\ (x, v) -> ( (between (text "|->")) <$> (pretty x) <*> (pretty v) ))

prettyDeps :: (Applicative m, LFresh m, MonadReader Size m) => [(Nom, Type)] -> m Doc
prettyDeps ns = (brackets . commaSep) <$> flip mapM ns
                    (\ (x, _T) -> ( (between (text ":")) <$> (pretty x) <*> (pretty _T) ))

prettyDefns :: (Applicative m, LFresh m, MonadReader Size m) => [(Nom, Type, VAL)] -> m Doc
prettyDefns ns = (brackets . commaSep) <$> flip mapM ns
                    (\ (x, _T, v) -> ( f <$> (pretty x) <*> (pretty _T) <*> (pretty v) ))
   where f x' _T' v' = x' <+> text ":=" <+> v' <+> text ":" <+> _T'

prettyParams :: (Applicative m, LFresh m, MonadReader Size m) => Params -> m Doc
prettyParams xs = vcat <$> flip mapM xs
                     (\ (x, p) -> ( (between colon) <$> (pretty x) <*> (pretty p) ) )



type Err = String

newtype Contextual a = Contextual { unContextual ::
    ReaderT Params (StateT Context (FreshMT (ErrorT Err Identity))) a }
  deriving (Functor, Applicative, Monad,
                Fresh, MonadError Err,
                MonadState Context, MonadReader Params,
                MonadPlus, Alternative)

ctrace :: String -> Contextual ()
ctrace s = do
    cx    <- get
    _Gam  <- ask
    trace (s ++ "\n" ++ pp cx ++ "\n---\n" ++ ppWith prettyParams _Gam)
          (return ()) >>= \ () -> return ()

runContextual :: Context -> Contextual a -> Either Err (a, Context)
runContextual cx = runIdentity . runErrorT . runFreshMT . flip runStateT cx . flip runReaderT [] . unContextual

modifyL :: (ContextL -> ContextL) -> Contextual ()
modifyL f = modify (\ (x, y) -> (f x, y))

modifyR :: (ContextR -> ContextR) -> Contextual ()
modifyR f = modify (\ (x, y) -> (x, f y))

pushL :: Entry -> Contextual ()
pushL e = --trace ("Push left " ++ prettyString e) $
  modifyL (:< e)

pushR :: Either Subs Entry -> Contextual ()
pushR (Left s)   = pushSubs s
pushR (Right e)  = --trace ("Push right " ++ prettyString e) $
 modifyR (Right e :)

pushSubs :: Subs -> Contextual ()
pushSubs []  = return ()
pushSubs n   = modifyR (\ cr -> if null cr then [] else Left n : cr)

popL :: Contextual Entry
popL = do
    cx <- getL
    case cx of
        (cx' :< e)  -> putL cx' >> return e
        B0          -> fail "popL ran out of context"

popR :: Contextual (Maybe (Either Subs Entry))
popR = do
    cx <- getR
    case cx of
        (x  : cx')  -> putR cx' >> return (Just x)
        []          -> return Nothing

getL :: MonadState Context m => m ContextL
getL = gets fst

getR :: Contextual ContextR
getR = gets snd

putL :: ContextL -> Contextual ()
putL x = modifyL (const x)

putR :: ContextR -> Contextual ()
putR x = modifyR (const x)


inScope :: MonadReader Params m => Nom -> Param -> m a -> m a
inScope x p = local (++ [(x, p)])

localParams :: (Params -> Params) -> Contextual a -> Contextual a
localParams f = local f

lookupVar :: MonadReader Params m => Nom -> Twin -> m Type
lookupVar x w = do
  vars <- ask
  look vars
  where
    look [] = fail $ "lookupVar: missing " ++ show x
    look ((y, e) : _) | x == y =
      case (e, w) of
        (P _T,         Only)   -> return _T
        (Twins _S _T,  TwinL)  -> return _S
        (Twins _S _T,  TwinR)  -> return _T
        _                      -> fail $ "lookupVar: evil twin"
    look (_ : _Gam)                      = look _Gam

lookupMeta :: MonadState Context m => Nom -> m Type
lookupMeta x = look =<< getL
  where
    look :: Monad m => ContextL -> m Type
    look B0 = fail $ "lookupMeta: missing " ++ show x
    look (cx  :< E y t _)  | x == y     = return t
                           | otherwise  = look cx
    look (cx  :< Prob _ _ _) = look cx

metaValue :: MonadState Context m => Nom -> m VAL
metaValue x = look =<< getL
  where
    look :: Monad m => ContextL -> m Type
    look B0 = fail $ "lookupMeta: missing " ++ show x
    look (cx  :< E y _ (DEFN val))  | x == y     = return val
                           | otherwise  = look cx
    look (cx  :< Prob _ _ _) = look cx




$(derive[''Problem, ''ProblemState, ''Dec, ''Entry, ''Equation, ''Param, ''ProbId])
