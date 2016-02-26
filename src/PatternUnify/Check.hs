--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE GADTs, KindSignatures, TemplateHaskell,
      FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
      UndecidableInstances, GeneralizedNewtypeDeriving,
      TypeSynonymInstances, ScopedTypeVariables, PatternSynonyms #-}

-- This module defines a typechecker and definitional equality test for a
-- simple Set-in-Set type theory.

module PatternUnify.Check where

import Prelude hiding (any, elem, notElem)

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Data.Foldable (any)

import Unbound.LocallyNameless

import PatternUnify.Kit
import PatternUnify.Tm
import PatternUnify.Context


data Tel where
    Stop  :: Tel
    Ask   :: Type -> Bind Nom Tel -> Tel
  deriving Show

instance Alpha Tel
instance Subst VAL Tel

askTel :: String -> Type -> Tel -> Tel
askTel x _S _T = Ask _S (bind (s2n x) _T)

supply :: Fresh m => Bind Nom Tel -> VAL -> m Tel
supply _T v = do  (x, tel) <- unbind _T
                  return $ subst x v tel


canTy :: (Can, [VAL]) -> Can -> Contextual Tel
canTy (Set, []) Set  =  return Stop
canTy (Set, []) c | c `elem` [Pi, Sig] = return $ askTel "S" SET $
                                             askTel "T" (mv "S" --> SET) $ Stop
canTy (Sig, [_S, _T]) Pair  = return $ askTel "s" _S $ askTel "t" (_T $$ mv "s") $ Stop
canTy (c, as) v = fail $ "canTy: canonical type " ++ pp (C c as) ++
                             " does not accept " ++ pp v


typecheck :: Type -> VAL -> Contextual Bool
typecheck _T t = (check _T t >> return True) `catchError`
                     (\ _ -> return False)

check :: Type -> VAL -> Contextual ()

check (C c as)    (C v bs)  =  do
                               tel <- canTy (c, as) v
                               checkTel tel bs

check (PI _S _T)  (L b)     =  do
                               (x, t) <- unbind b
                               inScope x (P _S) $ check (_T $$ var x) t

check _T          (N u as)  =  do
                               _U   <- infer u
                               _T'  <- checkSpine _U (N u []) as
                               eq   <- (_T <-> _T')
                               unless eq $ fail $ "Inferred type " ++ pp _T' ++
                                                  " of " ++ pp (N u as) ++
                                                  " is not " ++ pp _T

check (SET) (Nat) = return ()
check (SET) (Vec a n) = do
  check SET a
  check Nat n
check (SET) (Eq a x y) = do
  check SET a
  check a x
  check a y

check (Nat) Zero = return ()
check Nat (Succ k) = check Nat k

check (Vec a Zero) (VNil a') = do
  eq <- a <-> a'
  check SET a
  unless eq $ fail $ "check: Nil index " ++ (pp a') ++ " does not match type index " ++ (pp a)

check (Vec a (Succ n)) (VCons a' h t n') = do
  eq1 <- a <-> a'
  eq2 <- n <-> n'
  check SET a
  check a h
  check (Vec a n) t
  check n Nat
  unless eq1 $ fail $ "check: Cons type index " ++ (pp a') ++ " does not match type index " ++ (pp a)
  unless eq2 $ fail $ "check: Cons length index " ++ (pp n') ++ " does not match type index " ++ (pp n)

check (Eq a x1 x2) (ERefl a' x) = do
  eq1 <- a <-> a'
  eq2 <- x <-> x1
  eq3 <- x <-> x2
  check SET a
  check a x
  unless eq1 $ fail $ "check: Refl type index " ++ (pp a') ++ " does not match type index " ++ (pp a)
  unless eq2 $ fail $ "check: Refl value index " ++ (pp x) ++ " does not match index in type " ++ (pp x1)
  unless eq3 $ fail $ "check: Refl value index " ++ (pp x) ++ " does not match second index in type " ++ (pp x2)

check _T          (C c as)  =  fail $ "check: canonical inhabitant " ++ pp (C c as) ++
                                      " of non-canonical type " ++ pp _T

check _T          (L _)     =  fail $ "check: lambda cannot inhabit " ++ pp _T



infer :: Head -> Contextual Type
infer (Var x w)  = lookupVar x w
infer (Meta x)   = lookupMeta x



checkTel :: Tel -> [VAL] -> Contextual ()
checkTel Stop         []      = return ()
checkTel (Ask _S _T)  (s:ss)  = do  check _S s
                                    tel' <- supply _T s
                                    checkTel tel' ss
checkTel Stop         (_:_)   = fail "Overapplied canonical constructor"
checkTel (Ask _ _)    []      = fail "Underapplied canonical constructor"


checkSpine :: Type -> VAL -> [Elim] -> Contextual Type
checkSpine _T           _  []        = return _T
checkSpine (PI _S _T)   u  (A s:ts)  = check _S s >>
                                       checkSpine (_T $$ s) (u $$ s) ts
checkSpine (SIG _S _T)  u  (Hd:ts)   = checkSpine _S (u %% Hd) ts
checkSpine (SIG _S _T)  u  (Tl:ts)   = checkSpine (_T $$ (u %% Hd)) (u %% Tl) ts
checkSpine (Nat) u (elim@(NatElim m mz ms) : ts) = do
  check u Nat
  check m (Nat --> SET)
  check mz (m $$ Zero)
  let ln = string2Name "l"
      lv = var ln
  check ms (PI Nat $ (m $$ lv) --> m $$ (Succ lv))
  checkSpine (m $$ u) (u %% elim) ts
  
checkSpine ty           _  (s:_)     = fail $ "checkSpine: type " ++ pp ty
                                           ++ " does not permit " ++ pp s



quote :: Type -> VAL -> Contextual VAL
quote (PI _S _T)   f         =  do
                                x <- fresh (s2n "xq")
                                lam x <$> inScope x (P _S)
                                    (quote (_T $$ var x) (f $$ var x))

quote (SIG _S _T)  v         =  PAIR <$> quote _S (v %% Hd) <*>
                                    quote (_T $$ (v %% Hd)) (v %% Tl)

quote (C c as)     (C v bs)  = do  tel <- canTy (c, as) v
                                   bs' <- quoteTel tel bs
                                   return $ C v bs'

quote _T           (N h as)  = do  _S <- infer h
                                   quoteSpine _S (N h []) as

quote SET Nat = return Nat
quote SET (Vec a Zero) = Vec <$> quote SET a <*> quote Nat Zero
quote SET (Eq a x y) = Eq <$> quote SET a <*> quote a x <*> quote a y

quote Nat Zero = return Zero
quote Nat (Succ k) = Succ <$> quote Nat k
--TODO why not <->
quote (Vec a _) (VNil b) =
  if (a == b)
  then VNil <$> quote a SET --TODO check equal?
  else error "Bad quote NIL "
quote (Vec a (Succ n)) (VCons b h t m) =
  if (m /= n || a /= b)
  then error "Bad quote CONS"
  else VCons
    <$> quote SET a
    <*> quote a h
    <*> quote (Vec a n) t
    <*> quote Nat n

quote (Eq a x y) (ERefl b z) =
  if (x /= y && x /= z && a /= b)
  then error "Bad quote REFL"
  else ERefl <$> quote SET a <*> quote a x

quote _T           t         = error $ "quote: type " ++ pp _T ++
                                       " does not accept " ++ pp t


quoteTel :: Tel -> [VAL] -> Contextual [VAL]
quoteTel Stop         []      = return []
quoteTel (Ask _S _T)  (s:ss)  = do  s'   <- quote _S s
                                    tel  <- supply _T s
                                    ss'  <- quoteTel tel ss
                                    return $ s':ss'
quoteTel _            _       = error "quoteTel: arity error"


quoteSpine :: Type -> VAL -> [Elim] -> Contextual VAL
quoteSpine _T           u []        =  return u
quoteSpine (PI _S _T)   u (A s:as)  =  do
                                       s' <- quote _S s
                                       quoteSpine (_T $$ s') (u $$ s') as
quoteSpine (SIG _S _T)  u (Hd:as)   =  quoteSpine _S (u %% Hd) as
quoteSpine (SIG _S _T)  u (Tl:as)   =  quoteSpine (_T $$ (u %% Hd)) (u %% Tl) as
quoteSpine _T           u (s:_)     =  error $ "quoteSpine: type " ++ pp _T ++
                                               " of " ++ pp u ++
                                               " does not permit " ++ pp s



equal :: Type -> VAL -> VAL -> Contextual Bool
equal _T s t = do
    s'   <- quote _T s
    t'   <- quote _T t
    return $ s' == t'

(<->) :: Type -> Type -> Contextual Bool
_S <-> _T = equal SET _S _T

isReflexive :: Equation -> Contextual Bool
isReflexive (EQN _S s _T t) =do
    eq <- equal SET _S _T
    if eq  then  equal _S s t
           else  return False



checkProb :: ProblemState -> Problem -> Contextual ()
checkProb st p@(Unify (EQN _S s _T t)) = do
   check SET _S
   check _S s
   check SET _T
   check _T t
   if st == Solved
       then do  eq <- isReflexive (EQN _S s _T t)
                unless eq $ error $ "checkProb: not unified " ++ pp p
       else return ()
checkProb st (All (P _T) b) = do
    check SET _T
    (x, p) <- unbind b
    inScope x (P _T) $ checkProb st p
checkProb st (All (Twins _S _T) b) = do
    check SET _S
    check SET _T
    (x, p) <- unbind b
    inScope x (Twins _S _T) $ checkProb st p



validate :: (ProblemState -> Bool) -> Contextual ()
validate q = local (const []) $ do
    _Del' <- getR
    unless (null _Del') $ error "validate: not at far right"
    _Del <- getL
    help _Del `catchError` (error . (++ ("\nwhen validating\n" ++ pp (_Del, _Del'))))
    putL _Del
  where
    help :: ContextL -> Contextual ()
    help B0 = return ()
    help (_Del :< E x _ _) | any (x `occursIn`) _Del = throwError "validate: dependency error"
    help (_Del :< E _ _T HOLE)      = do  putL _Del
                                          check SET _T
                                          help _Del
    help (_Del :< E _ _T (DEFN v))  = do  putL _Del
                                          check SET _T
                                          check _T v
                                          help _Del
    help (_Del :< Prob _ p st)      = do  checkProb st p
                                          unless (q st) $ throwError "validate: bad state"
                                          help _Del



$(derive [''Tel])
