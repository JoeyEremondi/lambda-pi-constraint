{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
--
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Top.Interface.Substitution where

import Top.Interface.Basic (ErrorLabel (..))
import Top.Monad.Select
import Top.Monad.StateFix
import Top.Types

import qualified PatternUnify.Tm as Tm

------------------------------------------------------------------------
-- (I)  Class name and (dedicated) deselect function

data ClassSubst = ClassSubst

deSubst :: (Embedded ClassSubst (s (StateFixT s m)) t, Monad m) => Select t (StateFixT s m) a -> StateFixT s m a
deSubst = deselectFor ClassSubst

------------------------------------------------------------------------
-- (II)  Type class declaration

class Monad m => HasSubst m info | m -> info where

   -- |Make the state consistent. Only relevant for substitution states that
   -- can be inconsistent (for instance, the type graph substitution state).
   makeSubstConsistent :: m ()

   -- |Unify two terms. Supply additional information for this unification.
   unifyTerms        :: info -> Tm.VAL -> Tm.VAL -> m ()

   -- |Lookup the value of a type variable in the substitution
   findSubstForVar   :: Tm.Nom -> m Tm.VAL

   -- |Return a fixpoint substitution.
   fixpointSubst     :: m FixpointSubstitution

------------------------------------------------------------------------
-- (III)  Instance for solver monad

instance ( Monad m
         , Embedded ClassSubst (s (StateFixT s m)) t
         , HasSubst (Select t (StateFixT s m)) info
         ) =>
           HasSubst (StateFixT s m) info where

   makeSubstConsistent   = deSubst makeSubstConsistent
   unifyTerms info t1 t2 = deSubst (unifyTerms info t1 t2)
   findSubstForVar       = deSubst . findSubstForVar
   fixpointSubst         = deSubst fixpointSubst

------------------------------------------------------------------------
-- (IV)  Additional functions

unificationErrorLabel :: ErrorLabel
unificationErrorLabel = ErrorLabel "unification"

-- |Apply the substitution to a value that contains type variables (a
-- member of the Substitutable type class).
applySubst :: (Substitutable a, HasSubst m info) => a -> m a
applySubst a =
   do let var = ftv a
      tps <- mapM findSubstForVar var
      let sub = listToSubstitution (zip var tps)
      return (sub |-> a)
