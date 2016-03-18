{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}

-- This module defines some basic general purpose kit, in particular
-- backwards lists and a typeclass of things that can be pretty-printed.


module PatternUnify.Kit  (  bool
            ,  Bwd
            , pattern B0
            , pattern (:<)
            ,  (<><)
            ,  (<>>)
            ,  trail
            ,  Size(..)
            ,  prettyAt
            ,  prettyLow
            ,  prettyHigh
            ,  wrapDoc
            ,  runPretty
            ,  pp
            ,  ppWith
            ,  Pretty(..)
            ,  between
            ,  commaSep
            ,  module PP
            ,  PatternUnify.Kit.elem
            ,  PatternUnify.Kit.notElem
            , bind2
            , bind3
            , bind4
            , bind5
            , bind6
            ) where


import Control.Monad.Reader

import Text.PrettyPrint.HughesPJ as PP hiding (($$))
import Unbound.Generics.LocallyNameless

elem :: Eq a => a -> [a] -> Bool
elem x y = x `Prelude.elem` y

notElem :: Eq a => a -> [a] -> Bool
notElem x y = not $ PatternUnify.Kit.elem x y

bool :: a -> a -> Bool -> a
bool no yes b = if b then yes else no


--data Bwd a = B0 | Bwd a :< a
--  deriving (Eq, Show, Functor, Foldable)

type Bwd a = [a]
pattern B0 = []
pattern x :< y = y : x

(<><) :: Bwd a -> [a] -> Bwd a
xs <>< []       = xs
xs <>< (y : ys) = (xs :< y) <>< ys

(<>>) :: Bwd a -> [a] -> [a]
B0         <>> ys = ys
(xs :< x)  <>> ys = xs <>> (x : ys)
_  <>> _ = undefined

trail :: Bwd a -> [a]
trail = (<>> [])


data Size = ArgSize | AppSize | PiSize | LamSize
    deriving (Bounded, Enum, Eq, Ord, Show)

prettyAt ::
    (Pretty a, Applicative m, LFresh m, MonadReader Size m) => Size -> a -> m Doc
prettyAt sz = local (const sz) . pretty

prettyLow, prettyHigh ::
    (Pretty a, Applicative m, LFresh m, MonadReader Size m) => a -> m Doc
prettyLow   a = prettyAt minBound a
prettyHigh  a = prettyAt maxBound a

wrapDoc :: MonadReader Size m => Size -> m Doc -> m Doc
wrapDoc dSize md = do
    d <- md
    curSize <- ask
    return $ if dSize > curSize then parens d else d

runPretty :: ReaderT Size LFreshM a -> a
runPretty = runLFreshM . flip runReaderT maxBound

pp :: Pretty a => a -> String
pp = render . runPretty . pretty

ppWith :: (a -> ReaderT Size LFreshM Doc) -> a -> String
ppWith f = render . runPretty . f

class Pretty a where
    pretty :: (Applicative m, LFresh m, MonadReader Size m) => a -> m Doc

instance Pretty (Name x) where
    pretty n = return $ text $ show n --return $ text $ show (name2String n, name2Integer n)

instance (Pretty a, Pretty b) => Pretty (Either a b) where
    pretty (Left x)   = (text "Left" <+>) <$> pretty x
    pretty (Right y)  = (text "Right" <+>) <$> pretty y

instance Pretty () where
    pretty () = return $ text "()"

between :: Doc -> Doc -> Doc -> Doc
between d x y = x <+> d <+> y

commaSep :: [Doc] -> Doc
commaSep = hsep . punctuate comma

--from http://hackage.haskell.org/package/definitive-base-2.3/docs/src/Algebra-Monad-Base.html#bind3
bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f a b = join (f<$>a<*>b)

bind3 :: Monad m => (a -> b -> c -> m d) -> m a -> m b -> m c -> m d
bind3 f a b c = join (f<$>a<*>b<*>c)

bind4
  :: Monad m =>
  (t -> t1 -> t2 -> t3 -> m b)
  -> m t
  -> m t1
  -> m t2
  -> m t3
  -> m b
bind4 f ma mb mc md = do
  a <- ma
  b <- mb
  c <- mc
  d <- md
  f a b c d

bind5 :: (Monad m) => (t -> t1 -> t2 -> t3 -> t4 -> m b) -> m t -> m t1 -> m t2 -> m t3 -> m t4 -> m b
bind5 f ma mb mc md me = do
  a <- ma
  b <- mb
  c <- mc
  d <- md
  e <- me
  f a b c d e


bind6 :: (Monad m) => (t -> t1 -> t2 -> t3 -> t4 -> t5 -> m b) -> m t -> m t1 -> m t2 -> m t3 -> m t4 -> m t5 -> m b
bind6 f ma mb mc md me mf = do
  a <- ma
  b <- mb
  c <- mc
  d <- md
  e <- me
  ff <- mf
  f a b c d e ff
