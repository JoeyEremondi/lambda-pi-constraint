--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

-- This module defines terms and machinery for working with them
-- (including evaluation and occurrence checking).
module PatternUnify.Tm where

import Data.Foldable (foldlM)
import Data.Function (on)
import Data.List (unionBy)
import Data.List (union)
import qualified Data.Map as Map
import Data.Typeable
--import Debug.Trace (trace)
import GHC.Generics
import GHC.Stack (errorWithStackTrace)
import PatternUnify.Kit
import Prelude hiding (elem, notElem)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

prettyString :: (Pretty a)
             => a -> String
prettyString t = render $ runPretty $ pretty t

type Nom = Name VAL

freshNom :: Fresh m
         => m Nom
freshNom = fresh (s2n "x")

data VAL where
        L :: Bind Nom VAL -> VAL
        N :: Head -> [Elim] -> VAL
        C :: Can -> [VAL] -> VAL
--        Nat :: VAL
--        Fin :: VAL -> VAL
--        Vec :: VAL -> VAL -> VAL
--        Eq :: VAL -> VAL -> VAL -> VAL
--        Zero :: VAL
--        Succ :: VAL -> VAL
--        FZero :: VAL -> VAL
--        FSucc :: VAL -> VAL -> VAL
--        VNil :: VAL -> VAL
--        VCons :: VAL -> VAL -> VAL -> VAL -> VAL
--        ERefl :: VAL -> VAL -> VAL
    deriving (Show, Generic)

type Type = VAL

data Can
  = Set
  | Pi
  | Sig
  | Pair
  | CNat
  | CZero
  | CSucc
  | CVec
  | CNil
  | CCons
  | CEq
  | CRefl
  | CFin
  | CFZero
  | CFSucc
  deriving (Eq, Show, Generic, Ord)

data Twin
  = Only
  | TwinL
  | TwinR
  deriving (Eq, Show, Generic)

data Head
  = Var Nom
        Twin
  | Meta Nom
  deriving (Eq, Show, Generic)

data Elim
  = A VAL
  | Hd
  | Tl
  | NatElim VAL
            VAL
            VAL
  | VecElim VAL
            VAL
            VAL
            VAL
            VAL
  | EqElim VAL
           VAL
           VAL
           VAL
           VAL
  | FinElim VAL
            VAL
            VAL
            VAL
  deriving (Eq, Show, Generic)

instance Eq VAL where
  (==) = aeq

instance Alpha VAL

instance Alpha Can

instance Alpha Twin

instance Alpha Head

instance Alpha Elim

instance Subst VAL VAL where
  substs subList expr = runFreshM $ eval (Map.fromList subList) expr
  subst n u = substs [(n, u)]

dictSubsts :: Subs -> VAL -> VAL
dictSubsts subDict expr = runFreshM $ eval (subDict) expr

dictSubst :: Nom -> VAL -> VAL -> VAL
dictSubst n u = dictSubsts $ Map.singleton n u

instance Subst VAL Can

instance Subst VAL Twin

instance Subst VAL Head

instance Subst VAL Elim

doubleCol = text "::"

instance Pretty VAL where
  pretty (PI _S (L b)) =
    lunbind b $
    \( x, _T ) ->
      wrapDoc PiSize $
      if x `occursIn` _T --TODO put back?
         then (\x' _S' _T' ->
                 text "forall" <+> parens (x' <+> doubleCol <+> _S') <+> text " . " <+> parens _T') <$>
              prettyHigh x <*>
              prettyHigh _S <*>
              prettyAt ArgSize _T
         else between (text "->") <$> prettyAt AppSize _S <*>
              prettyAt PiSize _T
  -- >
  pretty (SIG _S (L b)) =
    lunbind b $
    \( x, _T ) ->
      wrapDoc PiSize $
      if x `occursIn` _T
         then (\x' _S' _T' ->
                 text "exists" <+> parens (x' <+> colon <+> _S') <+> text " . " <+> parens _T') <$>
              prettyHigh x <*>
              prettyHigh _S <*>
              prettyAt ArgSize _T
         else between (text "*") <$> prettyAt AppSize _S <*> prettyAt PiSize _T
  -- >
  pretty (L b) = wrapDoc LamSize $ (text "\\" <+>) <$> prettyLam b
    where prettyLam u =
            lunbind u $
            \( x, t ) ->
              do v <-
                   if True {-x `occursIn` t-}
                      then prettyLow x
                      else return (text "_")
                 case t of
                   L b' -> (v <+>) <$> prettyLam b'
                   _ -> (\t' -> v <+> text "." <+> t') <$> prettyAt LamSize t
  pretty (N h []) = pretty h
  pretty (N h as) =
    wrapDoc AppSize $
    (\h' as' -> h' <+> hsep as') <$> pretty h <*> mapM (prettyAt ArgSize) as
  pretty Nat = return $ text "Nat"
  pretty (Vec a n) =
    (\pa pn -> text "Vec" <+> parens pa <+> parens pn) <$> pretty a <*> pretty n
  pretty (Eq a x y) =
    (\pa px py -> text "Eq" <+> parens pa <+> parens px <+> parens py) <$> pretty a <*> pretty x <*>
    pretty y
  pretty Zero = return $ text "0"
  pretty nat@(Succ n) = prettyNat nat
  pretty (Fin n) = parens <$> (\pn -> text "Fin " <+> parens pn) <$> pretty n
  pretty (FZero n) = parens <$> (\pn -> text "FZero " <+> parens pn) <$> pretty n
  pretty (FSucc n f) =
    parens <$>
    ((\pn pf -> text "FSucc" <+> parens pn <+> parens pf ) <$>
     pretty n <*>
     pretty f)
  pretty (VNil a) = parens <$> (\pa -> text "Nil " <+> pa) <$> pretty a
  pretty (VCons a n h t) =
    (\pa pn ph pt ->text "Cons " <+> parens pa <+> parens pn <+> parens ph <+> parens pt) <$>
    pretty a <*>
    pretty n <*>
    pretty h <*>
    pretty t
  pretty (ERefl a x) =
    parens <$>
    ((\pa px -> text "Refl" <+> parens pa <+> parens px) <$> pretty a <*> pretty x)

  pretty (C c []) = pretty c
  pretty (C c as) =
    wrapDoc AppSize $
    (\c' as' -> c' <+> hsep as') <$> pretty c <*> mapM (prettyAt ArgSize) as

prettyNat x = helper x 0 id where
  helper Zero count pfn = return $ text (show count)
  helper (Succ n) count pfn =
    helper n (count + 1) (\baseVal -> text "Succ" <+> parens (pfn baseVal))
  helper x _ pfn = pfn <$> pretty x


instance Pretty Can where
  pretty c = return $ text $ show c

instance Pretty Twin where
  pretty Only = return $ empty
  pretty TwinL = return $ (text "^<")
  pretty TwinR = return $ (text "^>")

instance Pretty Head where
  pretty (Var x w) =
    do h1 <- (pretty x)
       h2 <- (pretty w)
       return $ h1 <> h2
  pretty (Meta x) = (text "?" <>) <$> pretty x

instance Pretty Elim where
  pretty (A a) = pretty a
  pretty Hd = return $ text "!"
  pretty Tl = return $ text "-"
  pretty (VecElim a m mn mc n) =
    parens <$>
    ((\a' m' mn' mc' n' -> text "VecElim" <+> a' <+> m' <+> mn' <+> mc' <+> n') <$>
     pretty a <*>
     pretty m <*>
     pretty mn <*>
     pretty mc <*>
     pretty n)
  pretty (NatElim m mz ms) =
    parens <$>
    ((\m' mz' ms' -> text "NatElim" <+> parens m' <+> parens mz' <+> parens ms') <$>
     pretty m <*>
     pretty mz <*>
     pretty ms)
  pretty (FinElim m mz ms n) =
    parens <$>
    ((\m' mz' ms' n' ->
        text "FinElim" <+>
        parens m' <+> parens mz' <+> parens ms' <+> parens n') <$>
     pretty m <*>
     pretty mz <*>
     pretty ms <*>
     pretty n)
  pretty (EqElim a m mr x y) =
    parens <$>
    ((\a' m' mr' x' y' ->
        text "EqElim" <+>
        parens a' <+> parens m' <+> parens mr' <+> parens x' <+> parens y') <$>
     pretty a <*>
     pretty m <*>
     pretty mr <*>
     pretty x <*>
     pretty y)

pattern SET = C Set []

pattern PI _S _T = C Pi [_S, _T]

pattern SIG _S _T = C Sig [_S, _T]

pattern PAIR s t = C Pair [s, t]

pattern Nat = C CNat []
pattern Zero = C CZero []
pattern Succ n = C CSucc [n]

pattern Fin n = C CFin [n]
pattern FZero n = C CFZero [n]
pattern FSucc n f = C CFSucc [n, f]

pattern Vec a n = C CVec [a,n]
pattern VNil a = C CNil [a]
pattern VCons a n h t = C CCons [a,n,h,t]

pattern Eq a x y = C CEq [a,x,y]
pattern ERefl a x = C CRefl [a,x]

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

lams' :: [( Nom, Type )] -> VAL -> VAL
lams' xs t = lams (map fst xs) t

lamK :: VAL -> VAL
lamK t = L (bind (s2n "_x") t)

_Pi :: Nom -> Type -> Type -> Type
_Pi x _S _T = PI _S (lam x _T)

_Pis :: [( Nom, Type )] -> Type -> Type
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

mapElimM :: (Monad m)
         => (VAL -> m VAL) -> Elim -> m Elim
mapElimM f (A a) = A <$> (f a)
mapElimM _ Hd = return Hd
mapElimM _ Tl = return Tl
mapElimM f (NatElim m mz ms) = NatElim <$> (f m) <*> (f mz) <*> (f ms)
mapElimM f (FinElim m mz ms n) =
  FinElim <$> (f m) <*> (f mz) <*> (f ms) <*> (f n)
mapElimM f (VecElim a m mn mc n) =
  VecElim <$> (f a) <*> (f m) <*> (f mn) <*> (f mc) <*> (f n)
mapElimM f (EqElim a m mr x y) =
  EqElim <$> (f a) <*> (f m) <*> (f mr) <*> (f x) <*> (f y)

mapElim :: (VAL -> VAL) -> Elim -> Elim
mapElim f (A a) = A (f a)
mapElim _ Hd = Hd
mapElim _ Tl = Tl
mapElim f (NatElim m mz ms) =
  NatElim (f m)
          (f mz)
          (f ms)
mapElim f (FinElim m mz ms n) =
  FinElim (f m)
          (f mz)
          (f ms)
          (f n)
mapElim f (VecElim a m mn mc n) =
  VecElim (f a)
          (f m)
          (f mn)
          (f mc)
          (f n)
mapElim f (EqElim a m mr x y) =
  EqElim (f a)
         (f m)
         (f mr)
         (f x)
         (f y)

headVar :: Head -> Nom
headVar (Var x _) = x
headVar (Meta x) = x

isVar :: VAL -> Bool
isVar v =
  case runFreshM (etaContract v) of
    N (Var _ _) [] -> True
    _ -> False

toVars :: [Elim] -> Maybe [Nom]
toVars = traverse (toVar . mapElim (runFreshM . etaContract))
  where toVar :: Elim -> Maybe Nom
        toVar (A (N (Var x _) [])) = Just x
        toVar _ = Nothing

linearOn :: VAL -> [Nom] -> Bool
linearOn _ [] = True
linearOn t (a:as) = not (a `occursIn` t && a `elem` as) && linearOn t as

initLast :: [x] -> Maybe ( [x], x )
initLast [] = Nothing
initLast xs = Just (init xs, last xs)

--
--TODO etaContract for custom elims?
etaContract :: (Fresh m)
            => VAL -> m VAL
etaContract (L b) =
  do ( y, t ) <- unbind b
     sub <- etaContract t
     case sub of
       N x as
         | Just ( bs, A (N (Var y' _) []) ) <- initLast as
         , y == y'
         , not (y `occursIn` bs) -> return $ N x bs
       t' -> return $ lam y t'
etaContract (N x as) = N x <$> (mapM (mapElimM etaContract) as)
etaContract (PAIR s t) =
  do sub1 <- etaContract s
     sub2 <- etaContract t
     case (sub1, sub2) of
       ( N x as, N y bs )
         | Just ( as', Hd ) <- initLast as
         , Just ( bs', Tl ) <- initLast bs
         , x == y
         , as' == bs' -> return $ N x as'
       ( s', t' ) -> return $ PAIR s' t'
etaContract (C c as) = C c <$> (mapM etaContract as)


occursIn :: (Alpha t, Typeable a)
         => Name a -> t -> Bool
x `occursIn` t = x `elem` toListOf fv t

data Strength
  = Weak
  | Strong
  deriving (Eq, Ord, Show)

data Occurrence
  = Flexible
  | Rigid Strength
  deriving (Eq, Ord, Show)

isStrongRigid :: Maybe Occurrence -> Bool
isStrongRigid (Just (Rigid Strong)) = True
isStrongRigid _ = False

isRigid :: Maybe Occurrence -> Bool
isRigid (Just (Rigid _)) = True
isRigid _ = False

isFlexible :: Maybe Occurrence -> Bool
isFlexible (Just Flexible) = True
isFlexible _ = False

fvs :: (Occurs t)
    => t -> [Nom]
fvs = frees False

fmvs :: (Occurs t)
     => t -> [Nom]
fmvs = frees True

class Occurs t  where
  occurrence :: [Nom] -> t -> Maybe Occurrence
  frees :: Bool -> t -> [Nom]

instance Occurs Nom where
  occurrence _ _ = Nothing
  frees _ _ = []

unions :: [[a]] -> [a]
unions = concat

instance Occurs VAL where
  occurrence xs (L (B _ b)) = occurrence xs b
  occurrence xs (C _ as) = occurrence xs as
  occurrence xs (N (Var y _) as)
    | y `elem` xs = Just (Rigid Strong)
    | otherwise = weaken <$> occurrence xs as
    where weaken (Rigid _) = Rigid Weak
          weaken Flexible = Flexible
  occurrence xs (N (Meta y) as)
    | y `elem` xs = Just (Rigid Strong)
    | otherwise = const Flexible <$> occurrence xs as
  --occurrence xs _ = Nothing --TODO occurrence cases
  frees isMeta (L (B _ t)) = frees isMeta t
  frees isMeta (C _ as) = unions (map (frees isMeta) as)
  frees isMeta (N h es) = unions (map (frees isMeta) es) `union` x
    where x =
            case h of
              Var v _
                | not isMeta && isFreeName v -> [v]
              Meta v
                | isMeta && isFreeName v -> [v]
              _ -> []

type OC = Occurrence

instance Occurs Elim where
  occurrence xs (A a) = occurrence xs a
  occurrence xs (NatElim m mz ms) =
    occurrence xs
               [m, mz, ms]
  occurrence xs (FinElim m mz ms n) =
    occurrence xs
               [m, mz, ms, n]
  occurrence xs (VecElim a m mn mc n) =
    occurrence xs
               [m, mn, mc, n, a]
  occurrence xs (EqElim a m mr x y) =
    occurrence xs
               [a, m, mr, x, y]
  occurrence _ _ = Nothing
  frees isMeta (A a) = frees isMeta a
  frees isMeta (NatElim m mz ms) =
    unions (map (frees isMeta)
                [m, mz, ms])
  frees isMeta (FinElim m mz ms n) =
    unions (map (frees isMeta)
                [m, mz, ms, n])
  frees isMeta (VecElim a m mn mc n) =
    unions (map (frees isMeta)
                [m, mn, mc, n, a])
  frees isMeta (EqElim a m mr x y) =
    unions (map (frees isMeta)
                [a, m, mr, x, y])
  frees _ _ = []

instance (Occurs a, Occurs b) => Occurs ( a, b ) where
  occurrence xs ( s, t ) =
    max (occurrence xs s)
        (occurrence xs t)
  frees isMeta ( s, t ) = frees isMeta s `union` frees isMeta t

instance (Occurs a, Occurs b, Occurs c) => Occurs ( a, b, c ) where
  occurrence xs ( s, t, u ) =
    maximum [occurrence xs s, occurrence xs t, occurrence xs u]
  frees isMeta ( s, t, u ) =
    unions [frees isMeta s, frees isMeta t, frees isMeta u]

instance Occurs a => Occurs [a] where
  occurrence _ [] = Nothing
  occurrence xs ys = maximum $ map (occurrence xs) ys
  frees isMeta = unions . map (frees isMeta)

type Subs = Map.Map Nom VAL

type SubsList = [( Nom, VAL )]

--Compose substitutions
compSubs :: Subs -> Subs -> Subs --TODO this is pointless converting to list
compSubs newDict oldDict =
  let new = Map.toList newDict
      old = Map.toList oldDict
  in Map.fromList $
     unionBy ((==) `on` fst)
             new
             (substs new old)

--Map.union new (Map.map (dictSubsts new) old)
eval :: (Fresh m)
     => Subs -> VAL -> m VAL
--eval g t | trace ("Eval " ++ pp t ++ "\n  Subs: " ++ show g) False = error "Eval"
eval g (L b) =
  do ( x, t ) <- unbind b
     sub <- eval g t
     return $ L (bind x sub)
eval g (N u as) =
  do elims <- mapM (mapElimM (eval g)) as
     evalHead g u %%% elims
eval g (C c as) = C c <$> (mapM (eval g) as)


evalHead :: Subs -> Head -> VAL
evalHead g hv =
  case Map.lookup (headVar hv)
                  g of
    Just u      --trace ("HEAD found " ++ show (pp hv, show g)) $
     ->
      u
    Nothing -> N hv []

elim :: (Fresh m)
     => VAL -> Elim -> m VAL
--elim h s | trace ("Elim " ++ pp h ++ " %%% " ++ pp s) False = error "Eval"
elim (L b) (A a) =
  do ( x, t ) <- unbind b
     eval (Map.singleton x a) t
elim (N u as) e = return $ N u $ as ++ [e]
elim (PAIR x _) Hd = return x
elim (PAIR _ y) Tl = return y
elim Zero (NatElim m mz ms) = return mz
elim (Succ l) theElim@(NatElim m mz ms) =
  do sub <- elim l theElim
     ms $$$ [l, sub]
elim (FZero k) (FinElim m mz _ _) = mz $$ k
elim (FSucc k f) theElim@(FinElim m _ ms _) =
  do sub <- elim f theElim
     ms $$$ [k, f, sub]
elim (VNil _) theElim@(VecElim a m mn mc n) = return mn
elim (VCons _ _ h t) theElim@(VecElim a m mn mc (Succ n)) =
  do sub <- elim t theElim
     mc $$$ [n, h, t, sub]
elim (ERefl _ z) theElim@(EqElim a m mr x y) = mr $$ z
elim t a = badElim $ "bad elimination of " ++ pp t ++ " by " ++ pp a

badElim s = errorWithStackTrace s

app :: (Nom) -> VAL -> VAL
app n x =
  N (Var n Only)
    [A x]

apps :: (Nom) -> [VAL] -> VAL
apps n xs = N (Var n Only) $ map A xs

($$) :: (Fresh m)
     => VAL -> VAL -> m VAL
f $$ a = elim f (A a)

($$$) :: (Fresh m)
      => VAL -> [VAL] -> m VAL
($$$) = foldlM ($$)

($*$) :: (Fresh m)
      => VAL -> [( Nom, a )] -> m VAL
f $*$ _Gam = f $$$ map (var . fst) _Gam

(%%) :: (Fresh m)
     => VAL -> Elim -> m VAL
(%%) = elim

(%%%) :: (Fresh m)
      => VAL -> [Elim] -> m VAL
(%%%) = foldlM (%%)

lam_ :: String -> (Nom -> VAL) -> VAL
lam_ s f =
  lam (s2n s)
      (f $ s2n s)

pi_ s str f = PI s $ lam_ str f

msType :: Nom -> VAL
msType m =
  (pi_ Nat "msArg" (\l -> (m `app` (var l)) --> ((m `app` (Succ $ var l)))))

vmType a =
  (pi_ Nat
       "vec_n"
       (\n ->
          (Vec (var a)
               (var n)) -->
          (SET)))

mnType a m = (m `apps` [Zero, (VNil $ var a)])

mcType a m =
  (pi_ Nat
       "vec_k"
       (\n ->
          pi_ (var a)
              "vec_x"
              (\x ->
                 pi_ (Vec (var a)
                          (var n))
                     "vec_xs"
                     (\xs ->
                        (m `apps` [var n, var xs]) -->
                        (m `apps`
                         [Succ (var n)
                         ,VCons (var a)
                                (var n)
                                (var x)
                                (var xs)])))))

vResultType m n xs = m `apps` [var n, var xs]

eqmType a =
  pi_ a
      "eq_x"
      (\x ->
         pi_ a
             "eq_y"
             (\y ->
                (Eq a
                    (var x)
                    (var y)) -->
                (SET)))

eqmrType a m =
  pi_ (var a)
      "eq_xmr"
      (\x ->
         m `apps`
         [var x
         ,var x
         ,ERefl (var a)
                (var x)])

eqResultType m x y eq = m `apps` [var x, var y, var eq]

finmType = pi_ (Nat) "finm_n" $ \n -> Fin (var n) --> SET

finmzType m =
  pi_ (Nat) "finmz_n" $ \n -> m `apps` [Succ $ var n, FZero $ var n]

finmsType m   --pi_ (Nat) "n" $ \n ->
   =
  pi_ Nat "finms_n" $
  \n ->
    pi_ (Fin $ var n) "finms_f" $
    \f ->
      (m `apps` [var n, var f]) -->
      (m `apps`
       [Succ $ var n
       ,FSucc (var n)
              (var f)])

finRetType m =
  pi_ Nat "finRet_n" $
  \n -> pi_ (Fin $ var n) "finRet_f" $ \f -> m `apps` [var n, var f]

--Same, but in a fresh monad
lamv_ :: (Fresh m)
      => String -> (VAL -> m VAL) -> m VAL
lamv_ s f =
  do ourNom <- fresh (s2n s)
     body <- f $ var ourNom
     return $ lam ourNom body

piv_ :: (Fresh m)
     => VAL -> String -> (VAL -> m VAL) -> m VAL
piv_ s str f = PI s <$> lamv_ str f

arrowv_ :: (Fresh m)
        => m VAL -> m VAL -> m VAL
arrowv_ ms mt =
  do s <- ms
     t <- mt
     return $ s --> t

ret_ :: (Fresh m)
     => a -> m a
ret_ = return

msVType m = (piv_ Nat "msArg" (\l -> (m $$ l) `arrowv_` (m $$ (Succ $ l))))

vmVType a =
  (piv_ Nat
        "vec_n"
        (\n ->
           (ret_ $
            Vec (a)
                (n)) `arrowv_`
           (ret_ SET)))

mnVType a m = (m $$$ [Zero, (VNil $ a)])

mcVType a m =
  (piv_ Nat
        "vec_k"
        (\n ->
           piv_ (a)
                "vec_x"
                (\x ->
                   piv_ (Vec (a)
                             (n))
                        "vec_xs"
                        (\xs ->
                           (m $$$ [n, xs]) `arrowv_`
                           (m $$$
                            [Succ n
                            ,VCons (a)
                                   (n)
                                   (x)
                                   (xs)])))))

vResultVType m n xs = m $$$ [n, xs]

eqmVType :: (Fresh m)
         => VAL -> m VAL
eqmVType a =
  piv_ a
       "eq_x"
       (\x ->
          piv_ a
               "eq_y"
               (\y ->
                  (ret_ $
                   Eq a
                      (x)
                      (y)) `arrowv_`
                  (ret_ SET)))

eqmrVType a m =
  piv_ (a)
       "eq_xmr"
       (\x ->
          m $$$
          [x
          ,x
          ,ERefl (a)
                 (x)])

eqResultVType m x y eq = m $$$ [x, y, eq]

finmVType :: (Fresh m)
          => m VAL
finmVType = piv_ (Nat) "finm_n" $ \n -> ret_ $ Fin (n) --> SET

finmzVType m = piv_ (Nat) "finmz_n" $ \n -> m $$$ [Succ $ n, FZero $ n]

finmsVType m   --piv_ (Nat) "n" $ \n ->
   =
  piv_ Nat "finms_n" $
  \n ->
    piv_ (Fin $ n) "finms_f" $
    \f ->
      (m $$$ [n, f]) `arrowv_`
      (m $$$
       [Succ $ n
       ,FSucc (n)
              (f)])

finRetVType m =
  piv_ Nat "finRet_n" $ \n -> piv_ (Fin $ n) "finRet_f" $ \f -> m $$$ [n, f]
