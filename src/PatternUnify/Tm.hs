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

import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Control.Monad (forM, mapM, zipWithM)

data Region =
  SourceRegion
    { regionFile   :: String
    , regionLine   :: Int
    , regionColumn :: Int }
  | BuiltinRegion
  deriving (Eq, Ord, Show, Generic)

instance Alpha Region

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
        VBot :: String -> VAL
        VChoice :: ChoiceId -> CUID -> Nom -> VAL -> VAL -> VAL
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

data ChoiceId = ChoiceId {choiceIdToName :: Nom, choiceRegion :: Region}
  deriving (Eq, Ord, Show, Generic)
instance Alpha ChoiceId

data CUID = CUID {cuidNom :: Nom}
  deriving (Eq, Ord, Show, Generic)
instance Alpha CUID

freshCUID :: (Fresh m) => m CUID
freshCUID = CUID <$> (fresh $ s2n "CUID")

type Type = VAL

--Lets us store neutral terms in our graph
data OrderedNeutral = OrderedNeutral Nom VAL
  deriving (Show, Generic)

makeOrdered :: (Fresh m) => VAL -> m OrderedNeutral
makeOrdered v = do
  x <- freshNom
  return $ OrderedNeutral x v 

instance Eq OrderedNeutral where
  (OrderedNeutral _ v1) == (OrderedNeutral _ v2) =
    untypedEqual v1 v2

instance Ord OrderedNeutral where
  compare (OrderedNeutral x1 v1) (OrderedNeutral x2 v2) =
    if (untypedEqual v1 v2) then
      EQ
    else if (x1 == x2) then
      error ("Non-equal terms with equal labels " ++ pp v1 ++ "   " ++ pp v2)
    else
      compare x1 x2


untypedEqual :: VAL -> VAL -> Bool
untypedEqual x y = runFreshM $ helper x y
  where
    elimHelper :: (Fresh m) => Elim -> Elim -> m Bool
    elimHelper (Elim c1 args1) (Elim c2 args2)
      | c1 /= c2 = return False
      | otherwise = List.and <$> zipWithM helper args1 args2
    helper :: (Fresh m) => VAL -> VAL -> m Bool
    helper f1@(L x) f2@(L y) = do
       n <- freshNom
       b1 <- f1 $$ var n
       b2 <- f2 $$ var n
       helper b1 b2
    helper (N h1 elims1) (N h2 elims2) =
      do
        let
          eqHead = case (h1, h2) of
            (Var x1 _, Var x2 _) -> x1 == x2
            _ -> error "Can't do untyped equal with metas"
        eqElims <- zipWithM elimHelper elims1 elims2
        return $ List.and (eqHead : eqElims)
    helper (C c1 args1) (C c2 args2)
      | c1 /= c2 = return False
      | otherwise = List.and <$> zipWithM helper args1 args2
    helper (VChoice x1 x2 x3 x4 x5) y = error "Should only untyped check flattened"
    helper _ _ = return False

-- data ElimRep =
--   ElimRep CanElim [ValRep]
--   deriving (Eq, Ord, Show, Generic)
--
-- data ValRep =
--   LRep Nom ValRep
--   | NRep Nom [ElimRep]
--   | CRep Can [ValRep]
--   deriving (Eq, Ord, Show, Generic)
--
-- toValRep :: (Fresh m) => VAL -> m ValRep
-- toValRep (L v) = do
--   (x, body) <- unbind v
--   newBody <- toValRep body
--   return $ LRep x newBody
-- toValRep (N h elims) =
--   case h of
--     (Var h1 _) -> NRep h1 (map toElimRep elims)
--     (Meta h) -> error "No ValRep for meta"
--   --NRep v1 <$> (mapM toElimRep elims)
-- toValRep (C v1 v2) = _
-- toValRep (VBot v) = _
-- toValRep (VChoice v1 v2 v3 v4 v5) = _
--
-- toElimRep :: (Fresh m) => Elim -> m ElimRep
-- toElimRep e = _


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
--  | NeutralGraphTerm ValRep --Only to be used in graph
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

data Elim = Elim CanElim [VAL]  | EBot String
  deriving (Eq, Show, Generic)

data CanElim =
  CA
  | CHd
  | CTl
  | CNatElim
  | CEqElim
  | CVecElim
  | CFinElim
  deriving (Eq, Show, Generic, Ord)

-- data Elim
--   = A VAL
--   | Hd
--   | Tl
--   | NatElim VAL
--             VAL
--             VAL
--   | VecElim VAL
--             VAL
--             VAL
--             VAL
--             VAL
--   | EqElim VAL
--            VAL
--            VAL
--            VAL
--            VAL
--   | FinElim VAL
--             VAL
--             VAL
--             VAL
--   deriving (Eq, Show, Generic)

instance Eq VAL where
  (==) = aeq

instance Alpha VAL

instance Alpha Can

instance Alpha Twin

instance Alpha Head

instance Alpha Elim

instance Alpha CanElim

instance Subst VAL CanElim

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

maybePar (PI _ _) = id
maybePar (SIG _ _) = id
maybePar (C _ []) = id
maybePar (N _ []) = id
maybePar tm = parens


instance Pretty VAL where
  pretty (VBot s) = return $ text "⊥"
  pretty (VChoice cid _ _ s t) =
    (\ ps pt -> text ("{{-" ++ show (choiceIdToName cid) ++ "-{") <> ps <> char ',' <+> pt <> text "}}}" )
      <$> pretty s <*> pretty t
  pretty (PI _S (L b)) =
    lunbind b $
    \( x, _T ) ->
      wrapDoc PiSize $
      if x `occursIn` _T --TODO put back?
         then (\x' _S' _T' ->
                 text "forall" <+> parens (x' <+> doubleCol <+> _S') <+> text " . " <+> _T') <$>
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
      (if x `occursIn` _T
         then (\x' _S' _T' ->
                 text "exists" <+> parens (x' <+> colon <+> _S') <+> text " . " <+> _T')
          else (\x' _S' _T' ->
                  text "Prod" <+> maybePar _S _S' <+> maybePar _T _T')) <$>
              prettyHigh x <*>
              prettyHigh _S <*>
              prettyAt ArgSize _T

  pretty (PI _S _T) =
    wrapDoc PiSize $
    ((\_S' _T' ->
                maybePar _S _S' <+> text "->" <+> maybePar _T _T')) <$>
            prettyHigh _S <*>
            prettyAt ArgSize _T

  pretty (SIG _S _T) =
    wrapDoc PiSize $
    ((\_S' _T' ->
                text "Prod" <+> maybePar _S _S' <+> maybePar _T _T')) <$>
            prettyHigh _S <*>
            prettyAt ArgSize _T

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
--  pretty (N h []) = pretty h
  pretty (N h as) = do
    h' <- pretty h
    let elimsText = prettyElims h' as
    wrapDoc AppSize elimsText
    -- (\h' as' -> h' <+> hsep as') <$> pretty h <*> mapM (prettyAt ArgSize) as
  -- pretty Nat = return $ text "Nat"
  -- pretty (Vec a n) =
  --   (\pa pn -> text "Vec" <+> maybePar a pa <+> maybePar n pn) <$> pretty a <*> pretty n
  -- pretty (Eq a x y) =
  --   (\pa px py -> text "Eq" <+> maybePar a pa <+> maybePar x px <+> maybePar y py) <$> pretty a <*> pretty x <*>
  --   pretty y
  -- pretty Zero = return $ text "0"
  -- pretty nat@(Succ n) = prettyNat nat
  -- pretty (Fin n) =  (\pn -> text "Fin " <+> maybePar n pn) <$> pretty n
  -- pretty (FZero n) =  (\pn -> text "FZero " <+> maybePar n pn) <$> pretty n
  -- pretty (FSucc n f) =
  --
  --   ((\pn pf -> text "FSucc" <+> maybePar n pn <+> parens pf ) <$>
  --    pretty n <*>
  --    pretty f)
  -- pretty (VNil a) = parens <$> (\pa -> text "Nil " <+> pa) <$> pretty a
  -- pretty (VCons a n h t) =
  --   (\pa pn ph pt ->text "Cons " <+> parens pa <+> parens pn <+> parens ph <+> parens pt) <$>
  --   pretty a <*>
  --   pretty n <*>
  --   pretty h <*>
  --   pretty t
  -- pretty (ERefl a x) =
  --   parens <$>
  --   ((\pa px -> text "Refl" <+> parens pa <+> parens px) <$> pretty a <*> pretty x)

  pretty (C c []) = pretty c
  pretty (C c as) =
    wrapDoc AppSize $
    (\c' as' -> c' <+> hsep as') <$> pretty c <*> mapM (\a -> maybePar a <$> (prettyAt ArgSize a)) as

--prettyElims :: (Monad m) => Doc -> [Elim] -> m Doc
--prettyElims :: (Monad m) => Doc -> [Elim] -> m Doc
prettyElims hdText elims =
  case elims of
    [] ->
      return hdText
    (A arg : rest) -> do
      arg' <- pretty arg --TODO parens?
      prettyElims (hdText <+> arg' ) rest
    (EBot _ : rest) -> do
      prettyElims (hdText <+> text "⊥" ) rest

    (Elim can args : rest ) -> do
      can' <- pretty can
      args' <- mapM pretty args
      prettyElims ((parens $ can' <+> hsep args') <+> hdText) rest
--prettyElims hdText elims = error $ "Bad pretty elims " ++ show hdText ++ " " ++ show elims


prettyNat x = helper x 0 id where
  helper Zero count pfn = return $ text (show count)
  helper (Succ n) count pfn =
    helper n (count + 1) (\baseVal -> text "Succ" <+> maybePar n (pfn baseVal))
  helper x _ pfn = pfn <$> pretty x


instance Pretty Can where
  pretty Set = return $ text "*"
  pretty Pi = return $ text "Pi"
  pretty Sig = return $ text "Sigma"
  pretty Pair = return $ text "Pair"
  pretty CNat = return $ text "Nat"
  pretty CZero = return $ text "Zero"
  pretty CSucc = return $ text "Succ"
  pretty CVec = return $ text "Vec"
  pretty CNil = return $ text "Nil"
  pretty CCons = return $ text "Cons"
  pretty CEq = return $ text "Eq"
  pretty CRefl = return $ text "Refl"
  pretty CFin = return $ text "Fin"
  pretty CFZero = return $ text "FZero"
  pretty CFSucc = return $ text "FSucc"
  --pretty c = return $ text $ show c

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
  pretty (Elim can args) =
    (\can' as' -> can' <+> hsep as') <$> pretty can <*> mapM pretty args
  pretty (EBot _) = return $ text "⊥"

instance Pretty CanElim where
  pretty CA = error "Should not pretty A"
  pretty CHd = return $ text $ "fst"
  pretty CTl = return $ text $ "snd"
  pretty CNatElim = return $ text $ "natElim"
  pretty CEqElim = return $ text $ "eqElim"
  pretty CVecElim = return $ text $ "vecElim"
  pretty CFinElim = return $ text $ "finElim"


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

pattern A x = Elim CA [x]
pattern Hd = Elim CHd []
pattern Tl = Elim CTl []
pattern NatElim m mz ms = Elim CNatElim [m, mz, ms]
pattern FinElim m mz ms n = Elim CFinElim [m, mz, ms, n]
pattern VecElim a m mn mc n = Elim CVecElim [a, m, mn, mc, n]
pattern EqElim a m mr x y = Elim CEqElim [a, m, mr, x, y]

pattern Con c = C c []

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
mapElimM f (Elim can args) = Elim can <$> mapM f args

mapElim :: (VAL -> VAL) -> Elim -> Elim
mapElim f (Elim can args) = Elim can $ map f args

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
  occurrence xs (VChoice _ _ _ s t) = occurrence xs [s,t]
  occurrence xs (N (Var y _) as)
    | y `elem` xs = Just (Rigid Strong)
    | otherwise = weaken <$> occurrence xs as
    where weaken (Rigid _) = Rigid Weak
          weaken Flexible = Flexible
  occurrence xs (N (Meta y) as)
    | y `elem` xs = Just (Rigid Strong)
    | otherwise = const Flexible <$> occurrence xs as
  occurrence xs (VBot s) = Nothing
  --occurrence xs _ = Nothing --TODO occurrence cases
  frees isMeta (VBot s) = []
  frees isMeta (L (B _ t)) = frees isMeta t
  frees isMeta (C _ as) = unions (map (frees isMeta) as)
  frees isMeta (VChoice _ _ _ s t) = unions (map (frees isMeta) [s,t])
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

joinErrors :: [Maybe String] -> Maybe String
joinErrors l =
  case Maybe.catMaybes l of
    [] -> Nothing
    lm@(_:_) -> (Just . (List.intercalate "\n") ) lm


containsBottom :: (Fresh m) => VAL -> m (Maybe String)
containsBottom (L v) = do
  (x,b) <- unbind v
  containsBottom b
containsBottom (N v1 elims) = joinErrors <$> mapM elimContainsBottom elims
containsBottom (C v1 args) = joinErrors <$> mapM containsBottom args
containsBottom (VChoice _ _ _ s t) = joinErrors <$> mapM containsBottom [s,t]
containsBottom (VBot s) = return $ Just s
--containsBottom (Choice v1 v2) = joinErrors <$> mapM containsBottom [v1,v2]

elimContainsBottom :: (Fresh m) => Elim -> m (Maybe String)
elimContainsBottom (Elim v1 args) = joinErrors <$> mapM containsBottom args
elimContainsBottom (EBot s) = return $ Just s


flattenChoiceGen :: (Fresh m) =>  (ChoiceId -> Maybe ((VAL,VAL) -> VAL)) -> VAL -> m VAL
flattenChoiceGen shouldFlatten (L t) = do
  (var, body) <- unbind t
  newBody <- flattenChoiceGen shouldFlatten  body
  return $ L $ bind var newBody
flattenChoiceGen shouldFlatten (N v elims) =
  N v <$> mapM (flattenChoiceElim shouldFlatten) elims
flattenChoiceGen shouldFlatten (C t1 t2) =
  C t1 <$> mapM (flattenChoiceGen shouldFlatten)  t2
flattenChoiceGen shouldFlatten (VBot t) = return $ VBot t
flattenChoiceGen shouldFlatten (VChoice cid cuid n t1 t2) =
  case shouldFlatten cid of
    Nothing ->  VChoice cid cuid n <$> flattenChoiceGen shouldFlatten t1 <*> flattenChoiceGen shouldFlatten t2
    Just f -> flattenChoiceGen shouldFlatten $ f (t1,t2)

flattenChoiceElim :: (Fresh m) => (ChoiceId -> Maybe ((VAL,VAL) -> VAL)) -> Elim -> m Elim
flattenChoiceElim shouldFlatten (Elim e1 e2) = Elim e1 <$> mapM (flattenChoiceGen shouldFlatten)  e2
flattenChoiceElim _ (EBot e) = return $ EBot e

flattenChoice :: (Fresh m) => VAL -> m VAL
flattenChoice = flattenChoiceGen $ \_ -> Just fst

unsafeFlatten :: VAL -> VAL
unsafeFlatten = runFreshM . flattenChoice

splitOnChoice :: (Fresh m) => ChoiceId -> VAL -> m (VAL,VAL)
splitOnChoice cid v = do
  (,)
    <$> flattenChoiceGen (\c -> if c == cid then Just fst else Nothing) v
    <*> flattenChoiceGen (\c -> if c == cid then Just snd else Nothing) v


isFirstOrder :: VAL -> Bool
isFirstOrder (L _) = False
isFirstOrder (N _ []) = True
isFirstOrder (N _ _) = False
isFirstOrder (C _ args) = List.and $ map isFirstOrder args
isFirstOrder (VBot _) = True

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
eval g (VChoice cid cuid n s t) =
  VChoice cid cuid n <$> eval g s <*> eval g t
eval g (VBot s) = return $ VBot s



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
elim (VChoice cid _ n s t) theElim = do
  cuid <- freshCUID
  VChoice cid cuid n <$> elim s theElim <*> elim t theElim
elim (VBot s) elim = return $ VBot s --TODO better error?
elim t a = return $ VBot $ "bad elimination of " ++ pp t ++ " by " ++ pp a

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
