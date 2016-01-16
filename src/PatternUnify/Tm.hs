--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE GADTs, KindSignatures, TemplateHaskell,
      FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
      UndecidableInstances, TypeSynonymInstances, ScopedTypeVariables
      , PatternSynonyms #-}

-- This module defines terms and machinery for working with them
-- (including evaluation and occurrence checking).

module PatternUnify.Tm where

import Prelude hiding (elem, notElem)

import Control.Applicative (pure, (<*>), (<$>))
import Data.List (unionBy)
import Data.Function (on)
import Data.Traversable (traverse)

import Unbound.LocallyNameless hiding (empty)
import Unbound.LocallyNameless.Name (isFree)
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Unbound.LocallyNameless.Types (GenBind(..))
import Unbound.Util (unions)

import PatternUnify.Kit

type Nom = Name VAL

freshNom :: Fresh m => m Nom
freshNom = fresh (s2n "x")


data VAL where
    L  :: Bind Nom VAL -> VAL --Lambda
    N  :: Head -> [Elim] -> VAL --Neutral term
    C  :: Can -> [VAL] -> VAL --Constructor values
    Nat :: VAL
    Vec :: VAL -> VAL -> VAL
    Eq :: VAL -> VAL -> VAL -> VAL
    Succ :: VAL -> VAL
    VNil :: VAL
    VCons :: VAL -> VAL -> VAL -> VAL -> VAL
    ERefl :: VAL
    AnnVal  :: VAL -> VAL -> VAL --Annotated Values --TODO need this?
  deriving Show

type Type = VAL

data Can = Set | Pi | Sig | Pair
  deriving (Eq, Show)

data Twin = Only | TwinL | TwinR
  deriving (Eq, Show)

data Head = Var Nom Twin | Meta Nom
  deriving (Eq, Show)

data Elim = A VAL | Hd | Tl
  | NatElim VAL VAL VAL | VecElim VAL VAL VAL VAL VAL | EqElim VAL VAL VAL VAL VAL
  deriving (Eq, Show)


instance Eq VAL where
    (==) = aeq

instance Alpha VAL
instance Alpha Can
instance Alpha Twin
instance Alpha Head
instance Alpha Elim

instance Subst VAL VAL where
    substs     = eval
    subst n u  = substs [(n, u)]

instance Subst VAL Can
instance Subst VAL Twin
instance Subst VAL Head
instance Subst VAL Elim

instance Pretty VAL where
    pretty (PI _S (L b)) =
      lunbind b $ \ (x, _T) ->
      wrapDoc PiSize $
      if x `occursIn` _T
      then (\ x' _S' _T' -> text "Pi" <+> parens (x' <+> colon <+> _S') <+> _T')
           <$> prettyHigh x <*> prettyHigh _S <*> prettyAt ArgSize _T
      else between (text "->") <$> prettyAt AppSize _S <*> prettyAt PiSize _T
-- >
    pretty (SIG _S (L b)) =
      lunbind b $ \ (x, _T) ->
      wrapDoc PiSize $
      if x `occursIn` _T
      then (\ x' _S' _T' -> text "Sig" <+> parens (x' <+> colon <+> _S') <+> _T')
           <$> prettyHigh x <*> prettyHigh _S <*> prettyAt ArgSize _T
      else between (text "*") <$> prettyAt AppSize _S <*> prettyAt PiSize _T
-- >
    pretty (L b) = wrapDoc LamSize $ (text "\\" <+>) <$> prettyLam b
      where
        prettyLam u = lunbind u $ \ (x, t) -> do
            v <- if x `occursIn` t then prettyLow x else return (text "_")
            case t of
                L b'  -> (v <+>) <$> prettyLam b'
                _     -> (\ t' -> v <+> text "." <+> t') <$> prettyAt LamSize t
    pretty (N h []) = pretty h
    pretty (N h as) = wrapDoc AppSize $
                          (\ h' as' -> h' <+> hsep as')
                          <$> pretty h <*> mapM (prettyAt ArgSize) as
    pretty (C c []) = pretty c
    pretty (C c as) = wrapDoc AppSize $
                          (\ c' as' -> c' <+> hsep as')
                          <$> pretty c <*> mapM (prettyAt ArgSize) as

instance Pretty Can where
    pretty c = return $ text $ show c

instance Pretty Twin where
    pretty Only   = return $ empty
    pretty TwinL  = return $ (text "^<")
    pretty TwinR  = return $ (text "^>")

instance Pretty Head where
    pretty (Var x w)  =  error "TODO pretty head" --(pretty x) <> (pretty w)
    pretty (Meta x)   = (text "?" <>) <$> pretty x

instance Pretty Elim where
    pretty (A a)  = pretty a
    pretty Hd     = return $ text "!"
    pretty Tl     = return $ text "-"



pattern SET           = C Set []
pattern PI _S _T      = C Pi [_S, _T]
pattern SIG _S _T     = C Sig [_S, _T]
pattern PAIR s t      = C Pair [s, t]


var :: Nom -> VAL
var x = N (Var x Only) []

twin :: Nom -> Twin -> VAL
twin x w = N (Var x w) []

meta :: Nom -> VAL
meta x = N (Meta x) []


lam :: Nom -> VAL -> VAL
lam x t = L (bind x t)

lams :: [Nom] -> VAL -> VAL
lams xs t = foldr lam t xs

lams' :: [(Nom, Type)] -> VAL -> VAL
lams' xs t = lams (map fst xs) t

lamK :: VAL -> VAL
lamK t = L (bind (s2n "_x") t)

_Pi :: Nom -> Type -> Type -> Type
_Pi x _S _T = PI _S (lam x _T)

_Pis :: [(Nom, Type)] -> Type -> Type
_Pis xs _T = foldr (uncurry _Pi) _T xs

(-->) :: Type -> Type -> Type
_S --> _T = _Pi (s2n "xp") _S _T
infixr 5 -->

_Sig :: Nom -> Type -> Type -> Type
_Sig x _S _T = SIG _S (lam x _T)

(*:) :: Type -> Type -> Type
_S *: _T = _Sig (s2n "xx") _S _T

vv :: String -> VAL
vv x = var (s2n x)

mv :: String -> VAL
mv x = meta (s2n x)

ll :: String -> VAL -> VAL
ll x = lam (s2n x)

_PI :: String -> VAL -> VAL -> VAL
_PI x = _Pi (s2n x)

_SIG :: String -> VAL -> VAL -> VAL
_SIG x = _Sig (s2n x)



mapElim :: (VAL -> VAL) -> Elim -> Elim
mapElim f  (A a)  = A (f a)
mapElim _  Hd     = Hd
mapElim _  Tl     = Tl

headVar :: Head -> Nom
headVar (Var x _)  = x
headVar (Meta x)   = x

isVar :: VAL -> Bool
isVar v = case etaContract v of
            N (Var _ _) []  -> True
            _               -> False

toVars :: [Elim] -> Maybe [Nom]
toVars = traverse (toVar . mapElim etaContract)
  where
    toVar :: Elim -> Maybe Nom
    toVar (A (N (Var x _) []))  = Just x
    toVar _                     = Nothing

linearOn :: VAL -> [Nom] -> Bool
linearOn _  []      = True
linearOn t  (a:as)  = not (a `occursIn` t && a `elem` as) && linearOn t as

initLast :: [x] -> Maybe ([x], x)
initLast []  = Nothing
initLast xs  = Just (init xs, last xs)
--
etaContract :: VAL -> VAL
etaContract (L b) = case etaContract t of
    N x as | Just (bs, A (N (Var y' _) [])) <- initLast as, y == y',
                 not (y `occursIn` bs) -> N x bs
    t' -> lam y t'
   where
     (y, t) = unsafeUnbind b
etaContract (N x as) = N x (map (mapElim etaContract) as)
etaContract (PAIR s t) = case (etaContract s, etaContract t) of
    (N x as, N y bs) | Just (as', Hd) <- initLast as,
                       Just (bs', Tl) <- initLast bs,
                       x == y,
                       as' == bs'  -> N x as'
    (s', t') -> PAIR s' t'
etaContract (C c as) = C c (map etaContract as)

occursIn :: (Alpha t, Rep a) => Name a -> t -> Bool
x `occursIn` t = error "OccursIn" --x `elem` fv t


data Strength   = Weak | Strong
  deriving (Eq, Ord, Show)

data Occurrence  = Flexible | Rigid Strength
  deriving (Eq, Ord, Show)

isStrongRigid :: Maybe Occurrence -> Bool
isStrongRigid (Just (Rigid Strong))  = True
isStrongRigid _                      = False

isRigid :: Maybe Occurrence -> Bool
isRigid (Just (Rigid _))  = True
isRigid _                 = False

isFlexible :: Maybe Occurrence -> Bool
isFlexible (Just Flexible)  = True
isFlexible _                = False

fvs :: (Collection c, Occurs t) => t -> c Nom
fvs = frees False

fmvs :: (Collection c, Occurs t) => t -> c Nom
fmvs = frees True

class Occurs t where
    occurrence  :: [Nom] -> t -> Maybe Occurrence
    frees       :: Collection c => Bool -> t -> c Nom

instance Occurs Nom where
    occurrence _ _ = Nothing
    frees _ _ = emptyC

instance Occurs VAL where
    occurrence xs (L (B _ b))  = occurrence xs b
    occurrence xs (C _ as)     = occurrence xs as
    occurrence xs (N (Var y _) as)
        | y `elem` xs  = Just (Rigid Strong)
        | otherwise    = weaken <$> occurrence xs as
      where  weaken (Rigid _)  = Rigid Weak
             weaken Flexible   = Flexible
    occurrence xs (N (Meta y) as)
        | y `elem` xs  = Just (Rigid Strong)
        | otherwise    = const Flexible <$> occurrence xs as

    frees isMeta (L (B _ t))  = frees isMeta t
    frees isMeta (C _ as)     = unions (map (frees isMeta) as)
    frees isMeta (N h es)     = unions (map (frees isMeta) es)
                                  `union` x
      where x = case h of
                    Var v _  | not isMeta && isFree v  -> singleton v
                    Meta v   | isMeta && isFree v      -> singleton v
                    _                                  -> emptyC

instance Occurs Elim where
   occurrence xs  (A a)  = occurrence xs a
   occurrence _   _      = Nothing
   frees isMeta  (A a)   = frees isMeta a
   frees _       _       = emptyC

instance (Occurs a, Occurs b) => Occurs (a, b) where
    occurrence xs (s, t) = max (occurrence xs s) (occurrence xs t)
    frees isMeta (s, t) = frees isMeta s `union` frees isMeta t

instance (Occurs a, Occurs b, Occurs c) => Occurs (a, b, c) where
    occurrence xs (s, t, u) = maximum [occurrence xs s, occurrence xs t, occurrence xs u]
    frees isMeta (s, t, u) = unions [frees isMeta s, frees isMeta t, frees isMeta u]

instance Occurs a => Occurs [a] where
    occurrence _   []  = Nothing
    occurrence xs  ys  = maximum $ map (occurrence xs) ys
    frees isMeta = unions . map (frees isMeta)


type Subs = [(Nom, VAL)]

compSubs :: Subs -> Subs -> Subs
compSubs new old = unionBy ((==) `on` fst) new (substs new old)

eval :: Subs -> VAL -> VAL
eval g (L b)   = L (bind x (eval g t))
                     where (x, t) = unsafeUnbind b
eval g (N u as)  = evalHead g u %%% map (mapElim (eval g)) as
eval g (C c as)  = C c (map (eval g) as)

evalHead :: Subs -> Head -> VAL
evalHead g hv = case lookup (headVar hv) g of
                       Just u   -> u
                       Nothing  -> N hv []

elim :: VAL -> Elim -> VAL
elim (L b)       (A a)  = eval [(x, a)] t where (x, t) = unsafeUnbind b
elim (N u as)    e      = N u $ as ++ [e]
elim (PAIR x _)  Hd     = x
elim (PAIR _ y)  Tl     = y
elim t           a      = error $ "bad elimination of " ++ pp t ++ " by " ++ pp a

($$) :: VAL -> VAL -> VAL
f $$ a = elim f (A a)

($$$) :: VAL -> [VAL] -> VAL
($$$) = foldl ($$)

($*$) :: VAL -> [(Nom, a)] -> VAL
f $*$ _Gam = f $$$ map (var . fst) _Gam

(%%) :: VAL -> Elim -> VAL
(%%) = elim

(%%%) :: VAL -> [Elim] -> VAL
(%%%) = foldl (%%)

$(derive[''VAL, ''Can, ''Elim, ''Head, ''Twin])
