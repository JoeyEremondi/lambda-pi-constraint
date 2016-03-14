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

import Debug.Trace (trace)

import GHC.Stack (errorWithStackTrace)

prettyString t = render $ runPretty $ pretty t

type Nom = Name VAL

freshNom :: Fresh m => m Nom
freshNom = fresh (s2n "x")


data VAL where
    L  :: Bind Nom VAL -> VAL --Lambda
    N  :: Head -> [Elim] -> VAL --Neutral term
    C  :: Can -> [VAL] -> VAL --Constructor values
    Nat :: VAL
    Fin :: VAL -> VAL
    Vec :: VAL -> VAL -> VAL
    Eq :: VAL -> VAL -> VAL -> VAL
    Zero :: VAL
    Succ :: VAL -> VAL
    FZero :: VAL -> VAL
    FSucc :: VAL -> VAL -> VAL
    VNil :: VAL -> VAL
    VCons :: VAL -> VAL -> VAL -> VAL -> VAL
    ERefl :: VAL -> VAL -> VAL
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
  | NatElim VAL VAL VAL | VecElim VAL VAL VAL VAL VAL | EqElim VAL VAL VAL VAL VAL | FinElim VAL VAL VAL VAL
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
      if x `occursIn` _T --TODO put back?
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
            v <- if True {-x `occursIn` t-} then prettyLow x else return (text "_")
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

    pretty Nat = return $ text "Nat"
    pretty (Vec a n )= (\pa pn -> text "Vec" <+> pa <+> pn) <$> pretty a <*> pretty n
    pretty (Eq a x y) = (\pa px py -> text "Eq" <+> pa <+> px <+> py) <$> pretty a <*> pretty x <*> pretty y

    pretty Zero = return $ text "0"
    pretty (Succ n) =  (\pn -> text "S(" <+> pn <+> text ")") <$> pretty n

    pretty (Fin n) = parens <$> (\pn -> text "Fin " <+> pn ) <$> pretty n
    pretty (FZero n) = parens <$> (\pn -> text "FZero " <+> pn ) <$> pretty n
    pretty (FSucc n f) =  parens <$> ((\pn pf -> text "FS(" <+> pn <+> text "," <+> pf <+> text ")") <$> pretty n <*> pretty f)

    pretty (VNil _) = return $ text "[]"
    pretty (VCons a n h t) = (\pa pn ph pt -> ph <+> (text "::{" <+> pa <+> pn <+> text "}") <+> pt)
      <$> pretty a <*> pretty n <*> pretty h <*> pretty t

    pretty (ERefl a x) = parens <$> ((\pa px -> text "Refl" <+> pa <+> px)
      <$> pretty a <*> pretty x)


    pretty _ = return $ text "prettyTODO"

instance Pretty Can where
    pretty c = return $ text $ show c

instance Pretty Twin where
    pretty Only   = return $ empty
    pretty TwinL  = return $ (text "^<")
    pretty TwinR  = return $ (text "^>")

instance Pretty Head where
    pretty (Var x w)  =  do
      h1 <- (pretty x)
      h2 <- (pretty w)
      return $ h1 <> h2
    pretty (Meta x)   = (text "?" <>) <$> pretty x

instance Pretty Elim where
    pretty (A a)  = pretty a
    pretty Hd     = return $ text "!"
    pretty Tl     = return $ text "-"
    pretty (VecElim a m mn mc n)  = parens <$>
      ((\a' m' mn' mc' n' -> text "VecElim" <+> a' <+> m' <+> mn' <+> mc' <+> n')
      <$> pretty a
      <*> pretty m
      <*> pretty mn
      <*> pretty mc
      <*> pretty n)

    pretty (NatElim m mz ms)  = parens <$>
      ((\m' mz' ms' -> text "NatElim" <+> parens m' <+> parens mz' <+> parens ms')
      <$> pretty m
      <*> pretty mz
      <*> pretty ms)

    pretty (FinElim m mz ms n)  = parens <$>
      ((\m' mz' ms' n' -> text "FinElim" <+> parens m' <+> parens mz' <+> parens ms' <+> parens n')
      <$> pretty m
      <*> pretty mz
      <*> pretty ms
      <*> pretty n)
    pretty (EqElim a m mr x y)  = parens <$>
      ((\a' m' mr' x' y' ->
        text "EqElim" <+> parens a' <+> parens m' <+> parens mr' <+> parens x' <+> parens y')
      <$> pretty a
      <*> pretty m
      <*> pretty mr
      <*> pretty x
      <*> pretty y)
{-
mapElim f (EqElim a m mr x y) = EqElim (f a) (f m) (f mr) (f x) (f y)
-}


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
mapElim f (NatElim m mz ms) = NatElim (f m) (f mz) (f ms)
mapElim f (FinElim m mz ms n) = FinElim (f m) (f mz) (f ms) (f n)
mapElim f (VecElim a m mn mc n) = VecElim (f a) (f m) (f mn) (f mc) (f n)
mapElim f (EqElim a m mr x y) = EqElim (f a) (f m) (f mr) (f x) (f y)

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
etaContract Nat = Nat
etaContract Zero = Zero
etaContract (Succ k) = Succ (etaContract k)

occursIn :: (Alpha t, Rep a) => Name a -> t -> Bool
x `occursIn` t = x `elem` fv t


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

    occurrence xs (Nat) = Nothing
    occurrence xs (Fin n) = occurrence xs n
    occurrence xs (Vec a n) = occurrence xs [a,n]
    occurrence xs (Eq a x y) =   occurrence xs [a,x,y]

    occurrence xs (Zero) = Nothing
    occurrence xs (Succ n) = occurrence xs n
    occurrence xs (FZero n) = occurrence xs n
    occurrence xs (FSucc n f) = occurrence xs [n,f]
    occurrence xs (VNil a) = occurrence xs a
    occurrence xs (VCons a n h t) = occurrence xs [a,n,h,t]
    occurrence xs (ERefl a x) = occurrence xs [a,x]

    occurrence xs _ = Nothing --TODO occurrence cases

    frees isMeta (L (B _ t))  = frees isMeta t
    frees isMeta (C _ as)     = unions (map (frees isMeta) as)
    frees isMeta (N h es)     = unions (map (frees isMeta) es)
                                  `union` x
      where x = case h of
                    Var v _  | not isMeta && isFree v  -> singleton v
                    Meta v   | isMeta && isFree v      -> singleton v
                    _                                  -> emptyC
    frees isMeta (Nat) = emptyC
    frees isMeta (Fin n) = frees isMeta n
    frees isMeta (Zero) = emptyC
    frees isMeta (Succ n) = frees isMeta n
    frees isMeta (FZero n) = frees isMeta n
    frees isMeta (FSucc n f) = (frees isMeta n `union` frees isMeta f)
    frees isMeta (Vec a n) = (frees isMeta a `union` frees isMeta n)
    frees isMeta (VNil a) = frees isMeta a
    frees isMeta (VCons a n h t) = unions (map (frees isMeta) [a,n,h,t])
    frees isMeta (Eq a x y) = unions (map (frees isMeta) [a,x,y])
    frees isMeta (ERefl a x) = unions (map (frees isMeta) [a,x])
    frees isMeta _ = emptyC --TODO frees cases

type OC = Occurrence

instance Occurs Elim where
   occurrence xs  (A a)  = occurrence xs a
   occurrence xs (NatElim m mz ms) = occurrence xs [m, mz, ms]
   occurrence xs (FinElim m mz ms n) = occurrence xs [m, mz, ms, n]
   occurrence xs (VecElim a m mn mc n ) = occurrence xs [m, mn, mc, n, a]
   occurrence xs (EqElim a m mr x y) = occurrence xs [a, m, mr, x, y]
   occurrence _   _      = Nothing
   frees isMeta  (A a)   = frees isMeta a
   frees isMeta  (NatElim m mz ms) = unions (map (frees isMeta) [m, mz, ms])
   frees isMeta  (FinElim m mz ms n) = unions (map (frees isMeta) [m, mz, ms, n])
   frees isMeta  (VecElim a m mn mc n ) = unions (map (frees isMeta) [m, mn, mc, n, a])
   frees isMeta  (EqElim a m mr x y) = unions (map (frees isMeta) [a, m, mr, x, y])
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
--eval g t | trace ("Eval " ++ pp t ++ "\n  Subs: " ++ show g) False = error "Eval"
eval g (L b)   = L (bind x (eval g t))
                     where (x, t) = unsafeUnbind b
eval g (N u as)  = evalHead g u %%% map (mapElim (eval g)) as
eval g (C c as)  = C c (map (eval g) as)

eval g Nat = Nat
eval g (Vec a n) = Vec (eval g a) (eval g n)
eval g (Eq a x y) = Eq (eval g a) (eval g x) (eval g y)
eval g (Fin n) = Fin (eval g n)

eval _ Zero = Zero
eval g (Succ n) = Succ (eval g n)
eval g (VCons a n h t) = VCons (eval g a) (eval g n) (eval g h) (eval g t)
eval g (ERefl a x) = ERefl (eval g a) (eval g x)

eval g (FZero n) = FZero $ eval g n
eval g (FSucc n f) = FSucc (eval g n) (eval g f)


eval g t = error $ "Missing eval case for " ++ show t

subLookup :: Nom -> Subs -> Maybe VAL
subLookup _ [] = Nothing
subLookup nm ((sn, sv) : rest) =
  if (name2String nm == name2String sn && name2Integer nm == name2Integer sn)
  then Just sv
  else subLookup nm rest


evalHead :: Subs -> Head -> VAL
evalHead g hv = case subLookup (headVar hv) g of
                       Just u   -> --trace ("HEAD found " ++ show (pp hv, show g)) $
                          u
                       Nothing  -> N hv []

elim :: VAL -> Elim -> VAL
--elim h s | trace ("Elim " ++ pp h ++ " %%% " ++ pp s) False = error "Eval"
elim (L b)       (A a)  =
  let
    (x, t) = unsafeUnbind b
  in
    --subst x a t
    --trace ("ELIM_SUBST " ++ show (pp t, pp x)) $ 
      eval [(x, a)] t
elim (N u as)    e      = N u $ as ++ [e]
elim (PAIR x _)  Hd     = x
elim (PAIR _ y)  Tl     = y
elim Zero (NatElim m mz ms) = mz
elim (Succ l) theElim@(NatElim m mz ms) = ms $$$ [l, elim l theElim]
elim (FZero k) (FinElim m mz _ _) = mz $$ k
elim (FSucc k f) theElim@(FinElim m _ ms _) = ms $$$ [k, f, elim f theElim]
--TODO elim for Vec Eq
elim t           a      = badElim $ "bad elimination of " ++ pp t ++ " by " ++ pp a

badElim s = errorWithStackTrace s

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

lam_ s f = lam (s2n s) (f $ vv s)
pi_ s str f = PI s $ lam_ str f

msType m = (pi_ Nat "msArg" (\ l -> (m $$ l) --> ((m $$ (Succ l)))))

vmType a =(pi_ Nat "vec_n" (\ n -> (Vec a n) --> ( SET)))

mnType a m = (m $$ Zero $$ (VNil a))

mcType a m = (pi_ Nat "vec_n" (\ n ->
      pi_ a "vec_x" (\ x ->
      pi_ (Vec a n) "vec_xs" (\ xs ->
      (m $$ n $$ xs) --> (
      m $$ Succ n $$ VCons a n x xs)))))

vResultType m n xs = m $$ n $$ xs

eqmType a = pi_ a "eq_x" (\ x -> pi_ a "eq_y" (\ y -> (Eq a x y) --> ( SET)))

eqmrType a m = pi_ a "eq_xmr" (\ x -> m $$$ [x, x, ERefl a x] )

eqResultType m x y eq = m $$$ [x, y, eq]

finmType = pi_ (Nat) "finm_n" $ \n ->
  Fin n --> SET

finmzType m = pi_ (Nat) "finmz_n" $ \n ->
  m $$$ [Succ n, FZero n]

finmsType m = --pi_ (Nat) "n" $ \n ->
  pi_ Nat "finms_n" $ \n ->
    pi_ (Fin n) "finms_f" $ \f ->
      (m $$$ [n, f]) --> (m $$$ [Succ n, FSucc n f])

finRetType m = pi_ Nat "finRet_n" $ \n -> pi_ (Fin n) "finRet_f" $ \f -> m $$$ [n, f]

$(derive[''VAL, ''Can, ''Elim, ''Head, ''Twin])
