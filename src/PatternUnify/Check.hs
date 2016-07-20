--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

-- This module defines a typechecker and definitional equality test for a
-- simple Set-in-Set type theory.

module PatternUnify.Check where

import Prelude hiding (any, elem, notElem)

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Unbound.Generics.LocallyNameless

import GHC.Generics

import PatternUnify.Context
import PatternUnify.Kit
import PatternUnify.Tm

import qualified Data.List as List

--import qualified Data.List as List

import Debug.Trace (trace)


data Tel where
    Stop  :: Tel
    Ask   :: Type -> Bind Nom Tel -> Tel
  deriving (Show, Generic)

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
canTy (Set, []) CNat = return Stop
canTy (Set, []) CFin = return $ askTel "n" Nat $ Stop
canTy (Set, []) CVec = return $ askTel "a" SET $ askTel "n" Nat $ Stop
canTy (Set, []) CEq = return $ askTel "a" SET $ askTel "x" (mv "a") $ askTel "y" (mv "a") $ Stop

canTy (Sig, [_S, _T]) Pair  = do
  appResult <- (_T $$ mv "s")
  return $ askTel "s" _S $ askTel "t" appResult $ Stop

canTy (CNat, []) CZero = return Stop
canTy (CNat, []) CSucc = return $ askTel "n" Nat $ Stop

canTy (CFin, [n]) CFZero = return $ askTel "n" Nat $ Stop
canTy (CFin, [Succ n]) CFSucc = return $ askTel "n" Nat $ askTel "f" (Fin n) Stop

canTy (CVec, [a,Zero]) CNil = return $ askTel "a" SET $ Stop
canTy (CVec, [a,Succ n]) CCons = return $ askTel "a" SET $
  askTel "n" Nat $
  askTel "h" a $
  askTel "t" (Vec a n ) $ Stop

canTy (CEq, [a,x,y]) CRefl =
  return $ askTel "a" SET $
  askTel  "x" a $ Stop

canTy (c, as) v = throwError $ "canTy: canonical type " ++ pp (C c as) ++
                             " does not accept " ++ pp v


typecheck :: Type -> VAL -> Contextual Bool
typecheck _T t =
  (do
      tequal <- equalize _T t t
      cbottom <- containsBottom tequal
      return $ case cbottom of
        Nothing -> True
        Just s -> False) `catchError` \s -> return False


makeTypeSafe :: Type -> VAL -> Contextual VAL
makeTypeSafe _T t = equalize _T t t


check _Tinit tinit =
  --trace ("****Checking value " ++ pp t ++ " with type " ++ pp _T) $
  do
    _T <- flattenChoice _Tinit
    t <- flattenChoice tinit
    tequal <- equalize _T t t
    cbottom <- containsBottom tequal
    case cbottom of
       Nothing -> return ()
       Just s -> throwError $ "Typechecking error for " ++ pp tequal
        ++ "\n" ++ s --TODO nicer errors

equalizeMany :: Type -> [VAL] -> Contextual VAL
equalizeMany _T [t1,t2] = equalize _T t1 t2
equalizeMany _T [t1] = equalize _T t1 t1
equalizeMany _T (t1 : rest) = do
  ttail <- equalizeMany _T rest
  equalize _T t1 ttail
equalizeMany _ [] = return $ VBot "Cannot equalize 0 values"

-- headsMatch :: Head -> Head -> Bool
-- headsMatch (Var v Only) (Var v2 Only) = v == v2
-- headsMatch (Var v TwinL) (Var v2 TwinR) = v == v2
-- headsMatch (Var v TwinR) (Var v2 TwinL) = v == v2
-- headsMatch h1 h2 = h1 == h2
--
-- matchHeads :: Head -> Head -> Head
-- matchHeads (Var v Only) (Var v2 Only) | v == v2 = (Var v Only)
-- matchHeads (Var v TwinL) (Var v2 TwinR) | v == v2 = (Var v Only)
-- matchHeads (Var v TwinR) (Var v2 TwinL) | v == v2 = (Var v Only)
-- matchHeads h1 h2 | h1 == h2 = h1
equalize :: Type -> VAL -> VAL -> Contextual VAL
equalize _T s t = do
  _Tflat <- flattenChoice _T
  tflat <- flattenChoice t
  equalize' _Tflat s tflat
  where
    equalize' :: Type -> VAL -> VAL -> Contextual VAL
    --equalize' _T t t2 | trace ("Equalizing " ++ pp _T ++ " ||| " ++ pp t ++ " ||| " ++ pp t2 ++ "\n** ") False = error "equalize'"

    equalize' (SET) (SET) (SET) = return SET

    equalize' _T          (N u as) (N v as2) | u == v = --headsMatch u v =
      --trace ("equalize' neutral " ++ show u ++ " " ++ show (map pp as) ++ ", " ++ show (map pp as2)) $
      do
         let umatched = u --matchHeads u v
         vars <- ask
         _U1   <- infer u
         _V1   <- infer v
         _U <- equalize' SET _U1 _V1
         spineResult <- equalizeSpine _U (N umatched []) as as2
         case spineResult of
           Right (as', _T')  -> do
             eq   <- --trace ("equalize'd spines " ++ show (map pp as') ++ " : " ++ pp _T') $
               (_T <-> _T') --TODO make fail
             case eq of
               True -> return $ N umatched as'
               False ->
                 return $ VBot $
                   "Didn't match expected type " ++ pp _T ++ " with inferred type " ++ pp _T'
                   ++ "\n After inferring head type " ++ pp _U
                   ++ "\nin value " ++ pp (N umatched as')
           Left s -> return $ VBot s
    equalize' (C c as)   (C v bs) (C v2 bs2) | v == v2  =  do
                                   tel <- canTy (c, as) v --TODO source of bias?
                                   C v <$> equalizeTel tel bs bs2

    -- equalize' (PI _S _T)  (L b) (L b2)     =  do
    --                                (x, t) <- unbind b
    --                                (y, t2) <- unbind b2
    --                                appRes <- (_T $$ var x)
    --                                tf <- equalize' appRes t t2
    --                                inScope x (P _S) $
    --                                  return $ L $ bind x t2 --TODO how to deal with var here?
    equalize' (PI _U _V) f g = do
        vars <- ask
        x <- fresh $ s2n "arg"
        fx <- f $$ var x
        gx <- g $$ var x
        _Vx <- _V $$ var x
        body <- --trace ("FN BODY " ++ pp fx ++ ", " ++ pp gx ++ " : " ++ pp _Vx) $
          localParams (++ [(x, P _U)]) $ equalize' _Vx fx gx
        --trace ("FN RET " ++ pp fx ++ ", " ++ pp gx ++ " : " ++ pp _Vx)  $
        return $ L $ bind x body



    equalize' (SET) (Nat) Nat = return Nat
    equalize' (SET) (Fin n) (Fin n2) = do
      Fin <$> equalize' Nat n n2
    equalize' (SET) (Vec a n) (Vec a2 n2) =
      Vec <$> equalize' SET a a2 <*> equalize' Nat n n2
    equalize' (SET) (Eq a x y) (Eq a2 x2 y2) =
      Eq
      <$> equalize' SET a a2
      <*> equalize' a x x2
      <*> equalize' a y y2

    equalize' (Nat) Zero Zero = return Zero
    equalize' Nat (Succ k) (Succ k2) =
      Succ <$> equalize' Nat k k2

    equalize' (Fin (Succ n)) (FZero n') (FZero n2) =
      FZero <$> equalizeMany Nat [n,n2,n']
      --unless eq $ throwError $ "equalize': FZero index " ++ (pp n') ++ " does not match type index " ++ (pp n)

    equalize' (Fin (Succ n)) (FSucc n' k) (FSucc n2 k2) = do
      FSucc <$> equalizeMany Nat [n, n', n2] <*> equalize' (Fin n) k k2
      --eq <- equal Nat n n'
      --unless eq $ throwError $ "equalize': FSucc index " ++ (pp n') ++ " does not match type index " ++ (pp n)

    equalize' (Vec a Zero) (VNil a') (VNil a2) =
      VNil <$> equalizeMany SET [a,a2,a']

    equalize' (Vec a (Succ n)) (VCons a' n' h t) (VCons a2 n2 h2 t2) =
      VCons <$> equalizeMany SET [a,a2,a'] <*> equalizeMany Nat [n,n',n2] <*> equalize' a h h2 <*> equalize' (Vec a n) t t2

    equalize' (Eq a x y) (ERefl a1 x1) (ERefl a2 x2) =
      ERefl <$> equalizeMany SET [a,a1,a2] <*> equalizeMany a [x,y,x1,x2]

    --Choices are ordered, we equalize' their parts
    --TODO which meta?
    equalize' _T (VChoice cid cuid n1 s1 t1) (VChoice _ _ _ s2 t2) =
      VChoice cid cuid n1 <$> equalize' _T s1 s2 <*> equalize' _T t1 t2

    equalize' _T (VBot s1) (VBot s2) = return $ VBot (s1 ++ "\n" ++ s2)

    equalize' _T t1 t2 =
      --trace ("equalize' Bottom " ++ pp _T ++ ", " ++ pp t1 ++ ", " ++ pp t2) $
      return $ VBot $
        "Cannot equalize' values " ++ pp t1 ++ ", " ++ pp t2 ++
        "\nof type " ++ pp _T



infer :: Head -> Contextual Type
infer (Var x w)  = flattenChoice =<< lookupVar x w
infer (Meta x)   = flattenChoice =<< lookupMeta x


-- The |bindInScope| and |bindsInScope| helper operations introduce a
-- binding or two and call the continuation with a variable of the given
-- type in scope.

-- bindInScope ::  Type -> Bind Nom VAL ->
--                   (Nom -> VAL -> Contextual VAL) ->
--                   Contextual (Bind Nom VAL)
-- bindInScope _T b f = do  (x, b') <- unbind b
--                          bind x <$> inScope x (P _T) (f x b')
-- -- >
-- bindsInScope ::  Type -> Bind Nom VAL -> Bind Nom VAL ->
--                    (Nom -> VAL -> VAL -> Contextual VAL) ->
--                    Contextual (Bind Nom VAL)
-- bindsInScope _T a b f = do  Just (x, a', _, b') <- unbind2 a b
--                             bind x <$> inScope x (P _T) (f x a' b')


equalizeTel :: Tel -> [VAL] -> [VAL] -> Contextual [VAL]
equalizeTel tel vals1 vals2 = equalizeTel' tel vals1 vals2 []
  where
    equalizeTel' Stop         [] [] accum      = return accum
    equalizeTel' (Ask _S _T)  (s1:ss1) (s2:ss2) accum  =
      do
        sf <- equalize _S s1 s2
        tel' <- supply _T sf
        equalizeTel' tel' ss1 ss2 (accum ++ [sf])
    equalizeTel' _ _ _ _ = return [VBot "Bad equalize tel"] --TODO better tel matches
    -- checkTel Stop         (_:_)   = throwError "Overapplied canonical constructor"
    -- checkTel (Ask _ _)    []      = throwError "Underapplied canonical constructor"


equalizeSpine :: Type -> VAL -> [Elim] -> [Elim] -> Contextual (Either String ([Elim], Type))
equalizeSpine _T u spine1 spine2 = trace ("EQ SPINE: " ++ prettyString _T ++ " ||| " ++ prettyString u ++ " ||| " ++ (show $ map prettyString spine1) ++ " ||| " ++ (show $ map prettyString spine2)) $  equalizeSpine' _T u spine1 spine2 []
  where
    equalizeSpine' :: Type -> VAL -> [Elim] -> [Elim] -> [Elim] -> Contextual (Either String ([Elim], Type))

    equalizeSpine' _T           u  [] [] accum = return $ Right  (accum, _T)

    equalizeSpine' (PI _S _T)   u  (A s:ts)  (A s2:ts2) accum  = do
      sf <- equalize _S s s2
      uf <- equalize (PI _S _T) u u
      (bind5 equalizeSpine' (_T $$ sf) (uf $$ sf) (return ts) (return ts2)
        (return $ accum ++ [A sf]))

    equalizeSpine' (SIG _S _T)  u  (Hd:ts) (Hd:ts2) accum   =
      bind5 equalizeSpine' (return _S) (u %% Hd) (return ts) (return ts2) (return $ accum ++ [Hd])

    equalizeSpine' (SIG _S _T)  u  (Tl:ts) (Tl:ts2) accum   =
      bind5 equalizeSpine'
        ((_T $$) =<< (u %% Hd)) (u %% Tl) (return ts) (return ts2)
        (return $ accum ++ [Tl])

    equalizeSpine' (Nat) u ((NatElim m mz ms) : ts) ((NatElim m2 mz2 ms2) : ts2) accum = do
      uf <- equalize Nat u u --TODO check throughout if carry on equalize results
      mf <- equalize (Nat --> SET) m m2
      mzf <- bind3 equalize (mf $$ Zero) (return mz) (return mz2)
      msf <- bind3 equalize (msVType mf) (return ms) (return ms2)
      let elim = NatElim mf mzf msf
      bind5 equalizeSpine' (mf $$ uf) (uf %% elim) (return ts) (return ts2)
        (return $ accum ++ [elim])

    equalizeSpine' (Fin n') u ((FinElim m mz ms n) : ts) ((FinElim m2 mz2 ms2 n2) : ts2) accum = do
      nf <- equalizeMany Nat [n,n',n2]
      mf <- equalize finmType m m2
      elim <-
        FinElim mf
        <$> bind3 equalize (finmzVType mf) (return mz) (return mz2)
        <*> bind3 equalize (finmsVType mf) (return ms) (return ms2)
        <*> return nf
      uf <- equalize (Fin nf) u u
      bind5 equalizeSpine' (m $$$ [n, uf]) (uf %% elim) (return ts) (return ts2)
        (return $ accum ++ [elim])

    equalizeSpine' (Vec a' n') u ((VecElim a m mn mc n) : ts) ((VecElim a2 m2 mn2 mc2 n2) : ts2) accum = do
      nf <- equalizeMany Nat [n,n2,n']
      af <- equalizeMany SET [a,a2,a']
      uf <- equalize (Vec af nf) u u
      mf <- bind3 equalize (vmVType af) (return m) (return m2)
      elim <-
        VecElim af mf
        <$> bind3 equalize (mnVType af mf) (return mn) (return mn2)
        <*> bind3 equalize (mcVType af mf) (return mc) (return mc2)
        <*> return nf
      bind5 equalizeSpine' (vResultVType mf nf uf) (uf %% elim) (return ts) (return ts2)
        (return $ accum ++ [elim])

    equalizeSpine' (Eq a' x' y') u ((EqElim a m mr x y) : ts) ((EqElim a2 m2 mr2 x2 y2) : ts2) accum = do
      af <- equalizeMany SET [a,a',a2]
      xf <- equalizeMany a [x,x2,x']
      yf <- equalizeMany a [y,y2,y']
      mf <- bind3 equalize (eqmVType af) (return m) (return m2)
      uf <- equalize (Eq a x y) u u
      elim <-
        EqElim af mf
        <$> bind3 equalize (eqmrVType af mf) (return mr) (return mr2)
        <*> return xf
        <*> return yf
      bind5 equalizeSpine' (eqResultVType mf xf yf uf) (uf %% elim) (return ts) (return ts2) (return $ accum ++ [elim])

    equalizeSpine' ty u  (s:ts) (s2:ts2) accum     =
      equalizeSpine'
        (VBot $ "Bad eliminator " ++ pp s ++ " for value " ++ pp u ++ " of type " ++ pp ty)
        (VBot $ "Bad eliminator " ++ pp s2 ++ " for value " ++ pp u ++ " of type " ++ pp ty)
        ts ts2 (accum ++ [EBot "TODO Elim 1"])
    equalizeSpine' w x y z accum = return $ Left "Equalize Spine error" --error $ "TODO better equalizeSpine cases " ++ show (w,x,y,z)
      --throwError $ "equalizeSpine': type " ++ pp ty
                                               -- ++ " does not permit " ++ pp s


equal :: Type -> VAL -> VAL -> Contextual Bool
equal _T s t = --trace ("Equal comparing " ++ pp _T ++ " ||| " ++ pp s ++ " ========= " ++ pp t) $
  do
    st <- equalize _T s t
    cb <- containsBottom st
    return $ case cb of
      Nothing -> True
      _ -> False

unsafeEqual :: [(Nom, Param)] -> Type -> VAL -> VAL -> Bool
unsafeEqual vars _T s t =
  let
    result =
      runContextual initContext $
      localParams (vars ++ ) $
      equal _T s t
  in case fst result of
    Left _ -> False
    Right b -> b



(<->) :: Type -> Type -> Contextual Bool
_S <-> _T = equal SET _S _T

isReflexive :: Equation -> Contextual Bool
isReflexive eqn@(EQN _S s _T t _) = --trace ("IsRelexive " ++ pp eqn) $
  do
    vars <- ask
    eq <- --trace ("IsReflexive vars " ++ show vars) $
      equal SET _S _T
    ret <- if eq  then  equal _S s t
           else  return False
    --trace ("IsReflexive " ++ show ret) $
    return ret

checkProb :: ProbId -> ProblemState -> Problem -> Contextual ()
--checkProb ident st p | trace ("@@@ checkProb " ++ show ident ++ " " ++ show st ++ " " ++ pp p) False = error "checkProb"
checkProb ident st p@(Unify q) = do
   setProblem ident
   currentSubs <- metaSubs
   qflat@(EQN _S s _T t info) <- flattenEquation q
   !_SVal <-  flattenChoice =<< eval currentSubs _S
   check SET _SVal
   sVal <- flattenChoice =<< eval currentSubs s
   check _SVal sVal
   _TVal <- flattenChoice =<< eval currentSubs _T
   check SET _TVal
   tVal <- flattenChoice =<< eval currentSubs t
   --trace ("Flattened to: " ++ List.intercalate "\n" (map pp [_S, s, _T, t])) $
   check _TVal tVal
   if st == Solved
   then do
     eq <- isReflexive (EQN _SVal sVal _TVal tVal info)
     unless eq $ throwError $ "checkProb: Solved Problem not reflexive " ++ pp p ++ "\n  actually checked " ++ pp (EQN _SVal sVal _TVal tVal info)
   else return ()
checkProb ident st (All (P _T) b) = do
    setProblem ident
    currentSubs <- metaSubs
    _TVal <- eval currentSubs _T
    check SET _TVal
    (x, p) <- unbind b
    inScope x (P _TVal) $ checkProb ident st p
checkProb ident st (All (Twins _S _T) b) = do
    setProblem ident
    currentSubs <- metaSubs
    _SVal <- eval currentSubs _S
    check SET _SVal
    _TVal <- eval currentSubs _T
    check SET _TVal
    (x, p) <- unbind b
    inScope x (Twins _SVal _TVal) $ checkProb ident st p


shouldValidate info = isCF info == Factual


validate :: ((ProblemState, EqnInfo) -> Bool) -> Contextual ()
validate q = local (const []) $ do
    _Del' <- getR
    unless (null _Del') $ throwError "validate: not at far right"
    _Del <- getL
    --trace ("Context before validating " ++ List.intercalate "\n" (map pp _Del)) $
    help _Del --`catchError` (throwError . (++ ("\nwhen validating\n" ++ show (_Del, _Del'))))
    putL _Del
  where
    help :: ContextL -> Contextual ()
    help B0 = return ()
    --TODO why is this so slow?
    --help (_Del :< E x _ _) | any (x `occursIn`) _Del = throwError "validate: dependency error"
    help (_Del :< E _ _T HOLE info)      = do
                                          putL _Del
                                          when (isCF info == Factual) $
                                            check SET _T
                                          help _Del
    help (_Del :< E _ _T (DEFN v) info)  =
      do  putL _Del
          when (isCF info == Factual) $
            (check SET _T >> check _T v)
          help _Del
    help (_Del :< Prob ident p st _)      = do
                                          when (shouldValidate $ probInfo p) $ checkProb ident st p
                                          unless (q (st, probInfo p)) $ throwError "validate: bad state"
                                          help _Del
    help _ = undefined
