{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TypeSynonymInstances      #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
--
-- This module contains a data type to represent (plain) types, some basic
-- functionality for types, and an instance for Show.
--
-----------------------------------------------------------------------------

module Top.Types.Substitution where

import Data.List (nub, union, (\\))
import qualified Data.Map as M
import qualified Data.Set as S
import Top.Types.Primitive
import Utils (internalError)

import qualified PatternUnify.Tm as Tm
import qualified Unbound.Generics.LocallyNameless as Ln

----------------------------------------------------------------------
-- * Substitutions and substitutables

infix 4 |->

class Substitution s where
   lookupInt   :: Tm.Nom -> s -> Tm.VAL         -- lookup the type of a type variable in a substitution
   removeDom   :: [Tm.Nom] -> s -> s        -- remove from the domain of the substitution
   restrictDom :: [Tm.Nom] -> s -> s        -- restrict the domain of the substitution
   dom         :: s -> [Tm.Nom]             -- domain of substitution
   cod         :: s -> [Tm.VAL]               -- co-domain of substitution

class Substitutable a where
   (|->)       :: Substitution s => s -> a -> a   -- apply substitution
   ftv         :: a -> [Tm.Nom]                      -- free type variables

-- |The next type variable that is not free (default is zero)
nextFTV :: Substitutable a => a -> Tm.Nom
nextFTV a = case ftv a of
               [] -> error "start TV" --0
               is -> error "incr TV" -- maximum is + 1

----------------------------------------------------------------------
-- * Substitution instances

-- |A substitution represented by a finite map.
type MapSubstitution = M.Map Tm.Nom Tm.VAL

instance Substitution MapSubstitution where

   lookupInt i    = M.findWithDefault (Tm.var i) i
   removeDom      = flip (foldr M.delete)
   restrictDom is = let set = S.fromList is
                    in M.filterWithKey (\i _ -> S.member i set)

   dom = M.keys
   cod = M.elems

emptySubst :: MapSubstitution
emptySubst = M.empty

-- |Compose two finite map substitutions: safe.
-- Note for 'M.union': bindings in right argument shadow those in the left
(@@) :: MapSubstitution -> MapSubstitution -> MapSubstitution
fm1 @@ fm2 = fm1 `M.union` M.map (\t -> fm1 |-> t) fm2

-- |Compose two finite map substitutions: quick and dirty!
(@@@) :: MapSubstitution -> MapSubstitution -> MapSubstitution
(@@@) = M.union

singleSubstitution :: Tm.Nom -> Tm.VAL -> MapSubstitution
singleSubstitution = M.singleton

listToSubstitution :: [(Tm.Nom,Tm.VAL)] -> MapSubstitution
listToSubstitution = M.fromList

-- |A fixpoint is computed when looking up the target of a type variable in this substitution.
-- Combining two substitutions is cheap, whereas a lookup is more expensive than the
-- normal finite map substitution.
newtype FixpointSubstitution = FixpointSubstitution (M.Map Tm.Nom Tm.VAL)

instance Substitution FixpointSubstitution where
   lookupInt i original@(FixpointSubstitution fm) =
      case M.lookup i fm of
         Just tp | tp == Tm.var i -> Tm.var i
                 | otherwise    -> original |-> tp
         Nothing                -> Tm.var i
   removeDom   is (FixpointSubstitution fm) = FixpointSubstitution (M.filterWithKey (\i _ -> i `notElem` is) fm)
   restrictDom is (FixpointSubstitution fm) = let js = M.keys fm \\ is
                                              in FixpointSubstitution (M.filterWithKey (\i _ -> i `notElem` js) fm)
   dom (FixpointSubstitution fm) = M.keys fm
   cod (FixpointSubstitution fm) = M.elems fm

-- |The empty fixpoint substitution
emptyFPS :: FixpointSubstitution
emptyFPS = FixpointSubstitution M.empty

-- |Combine two fixpoint substitutions that are disjoint
disjointFPS :: FixpointSubstitution -> FixpointSubstitution -> FixpointSubstitution
disjointFPS (FixpointSubstitution fm1) (FixpointSubstitution fm2) =
   let notDisjoint = internalError "Substitution" "disjointFPS" "the two fixpoint substitutions are not disjoint"
   in FixpointSubstitution (M.unionWith notDisjoint fm1 fm2)

----------------------------------------------------------------------
-- * Wrapper for substitutions

wrapSubstitution :: Substitution substitution => substitution -> WrappedSubstitution
wrapSubstitution substitution =
   WrappedSubstitution substitution
      ( lookupInt
      , removeDom
      , restrictDom
      , dom
      , cod
      )

data WrappedSubstitution =
   forall a . Substitution a =>
      WrappedSubstitution a
         ( Tm.Nom -> a -> Tm.VAL
         , [Tm.Nom] -> a -> a
         , [Tm.Nom] -> a -> a
         , a -> [Tm.Nom]
         , a -> [Tm.VAL]
         )

instance Substitution WrappedSubstitution where
   lookupInt   i  (WrappedSubstitution x (f,_,_,_,_)) = f i x
   removeDom   is (WrappedSubstitution x (_,f,_,_,_)) = wrapSubstitution (f is x)
   restrictDom is (WrappedSubstitution x (_,_,f,_,_)) = wrapSubstitution (f is x)
   dom            (WrappedSubstitution x (_,_,_,f,_)) = f x
   cod            (WrappedSubstitution x (_,_,_,_,f)) = f x

----------------------------------------------------------------------
-- * Substitutables instances

instance Substitutable Tm.VAL where
   sub |-> tp =
      error "sub"
   ftv tp =
      error "ftv"

instance Substitutable a => Substitutable [a] where
   sub |-> as = map (sub |->) as
   ftv        = foldr (union . ftv) []

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
   sub |-> (a, b) = (sub |-> a, sub |-> b)
   ftv (a, b)     = ftv a `union` ftv b

instance Substitutable a => Substitutable (Maybe a) where
   sub |-> ma  = fmap (sub |->) ma
   ftv         = maybe [] ftv

instance (Substitutable a, Substitutable b) => Substitutable (Either a b) where
   sub |-> x = either (Left . (sub |->)) (Right . (sub |->)) x
   ftv       = either ftv ftv

freezeFTV :: Substitutable a => a -> a
freezeFTV a =
   let sub = listToSubstitution [ (i, error "freeze" ('_':show i)) | i <- ftv a ]
   in sub |-> a

allTypeVariables :: HasTypes a => a -> [Tm.Nom]
allTypeVariables = ftv . getTypes

allTypeConstants :: HasTypes a => a -> [String]
allTypeConstants =
  let f = error "allTypeConstants"
  --  let f (TVar _)   = []
  --      f (TCon s)   = [s]
  --      f (TApp l r) = f l ++ f r
   in nub . concatMap f . getTypes
