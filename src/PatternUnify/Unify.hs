-- %if False
--{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module PatternUnify.Unify where

import Control.Monad (forM)
import Control.Monad.Except (catchError, throwError, when)
import Control.Monad.Reader (ask)
import Data.List ((\\))
import qualified Data.Map as Map
import Data.Maybe (isNothing)
import Data.Set (Set, isSubsetOf)
import Prelude hiding (elem, notElem)
--import qualified Data.List as List
import qualified Data.Set as Set
import PatternUnify.Check (check, checkProb, equal, isReflexive, typecheck, makeTypeSafe)
import PatternUnify.Context (Contextual, Dec (..), Entry (..), Equation (..),
                             Param (..), ProbId (..), Problem (..),
                             ProblemState (..), addEqn, allProb, allTwinsProb,
                             localParams, lookupMeta, lookupVar, modifyL, popL,
                             popR, pushL, pushR, setProblem,
                             wrapProb, EqnInfo(..))
import qualified PatternUnify.Context as Ctx
import PatternUnify.Kit (bind3, bind4, bind6, bind7, elem, notElem, pp)
import PatternUnify.Tm
import Unbound.Generics.LocallyNameless (Fresh, runFreshM, subst, substs,
                                         unbind)

import qualified Top.Implementation.TypeGraph.ClassMonadic as CM
import qualified Top.Implementation.TypeGraph.Standard as TG

import Debug.Trace (trace)

notSubsetOf :: Ord a
            => Set a -> Set a -> Bool
a `notSubsetOf` b = not (a `isSubsetOf` b)

vars :: (Ord a)
     => [( a, b )] -> [a]
vars x = map fst x

active :: ProbId -> Equation -> Contextual ()
block :: ProbId -> Equation -> Contextual ()
failed
  :: ProbId -> Equation -> String -> Contextual ()
solved :: ProbId -> Equation -> Contextual ()
simplify
  :: ProbId -> Problem -> [Problem] -> Contextual ()
active n q = putProb n (Unify q) Active

block n q = putProb n (Unify q) Blocked

failed n q e =
  putProb n
          (Unify q)
          (Failed e)

solved n q =
  pendingSolve n
               (Unify q)
               []

putProb
  :: ProbId -> Problem -> ProblemState -> Contextual ()
putProb x q s =
  do setProblem x
     _Gam <- ask
     pushR . Right $ Prob x (wrapProb _Gam q) s

pendingSolve
  :: ProbId -> Problem -> [ProbId] -> Contextual ()
pendingSolve n q [] =
  do setProblem n
     checkProb n Solved q `catchError`
       (throwError . (++ "when checking problem " ++ pp n ++ " : " ++ pp q))
     putProb n q Solved
pendingSolve n q ds = putProb n q (Pending ds)

simplify n q rs = setProblem n >> help rs []
  where help
          :: [Problem] -> [ProbId] -> Contextual ()
        help [] xs = pendingSolve n q xs
        help (p:ps) xs = subgoal p (\x -> help ps (x : xs))
        -- >
        subgoal
          :: Problem -> (ProbId -> Contextual a) -> Contextual a
        subgoal p f =
          do x <- ProbId <$> freshNom
             _Gam <- ask
             pushL $ Prob x (wrapProb _Gam p) Active
             a <- f x
             goLeft
             return a

goLeft :: Contextual ()
goLeft = popL >>= pushR . Right

hole
  :: EqnInfo -> [( Nom, Type )] -> Type -> (VAL -> Contextual a) -> Contextual a
define
  :: EqnInfo -> [( Nom, Type )] -> Nom -> Type -> VAL -> Contextual ()
hole info _Gam _T f =
  do check SET (_Pis _Gam _T) `catchError`
       (throwError . (++ "\nwhen creating hole of type " ++ pp (_Pis _Gam _T)))
     x <- freshNom
     pushL $ E x (_Pis _Gam _T) HOLE info
     a <- f =<< (N (Meta x) [] $*$ _Gam)
     goLeft
     return a

defineGlobal
  :: EqnInfo -> Nom -> Type -> VAL -> Contextual a -> Contextual a
defineGlobal info x _T vinit m = --trace ("Defining global " ++ show x ++ " := " ++ pp vinit ++ " : " ++ pp _T) $
  do --hole (info {-isCF = CounterFactual-}) [] _T $ \freshVar@(N (Meta newNom) _) -> do
     ctxr <- Ctx.getR
     vsingle <- makeTypeSafe _T vinit

     let v = vinit --trace ("Fresh choice var " ++ show freshVar) $ VChoice vsingle freshVar
     --check _T v `catchError`
     --   (throwError .
     --    (++ "\nwhen defining " ++ pp x ++ " : " ++ pp _T ++ " to be " ++ pp v))
     pushL $ E x _T (DEFN v) info
     pushR (Left (Map.singleton x v))
     a <- m
     goLeft
     --Ctx.moveDeclRight x newNom
     --Add our final value to the type graph
     Ctx.recordEqn (Ctx.DefineMeta x) (EQN _T (meta x) _T v info)
     return a

define pid _Gam x _T v =
  defineGlobal pid x
               (_Pis _Gam _T)
               (lams' _Gam v)
               (return ())

-- %endif
-- \subsection{Unification}
-- \label{subsec:impl:unification}
-- As we have seen, unification splits into four main cases:
-- $\eta$-expanding elements of $\Pi$ or $\Sigma$ types, rigid-rigid
-- equations between non-metavariable terms (Figure~\ref{fig:decompose}),
-- flex-rigid equations between a metavariable and a rigid term
-- (Figure~\ref{fig:flex-rigid}), and flex-flex equations between two
-- metavariables (Figure~\ref{fig:flex-flex}). When the equation is
-- between two functions, we use twins (see
-- subsection~\ref{subsec:twins}) to decompose it heterogeneously. If it
-- is in fact homogeneous, the twins will be simplified away later.
-- We will take slight liberties, here and elsewhere, with the Haskell
-- syntax. In particular, we will use italicised capital letters (e.g.\
-- |_A|) for Haskell variables representing types in the object language,
-- while sans-serif letters (e.g.\ |A|) will continue to stand for data
-- constructors.
eqn
  :: (Fresh m)
  => m Type -> m VAL -> m Type -> m VAL -> m EqnInfo -> m Equation
eqn ma mx mb my mpid =
  do a <- ma
     b <- mb
     x <- mx
     y <- my
     pid <- mpid
     return $ EQN a x b y pid --TODO keep probId?

munify :: (Fresh m)
       => m Equation -> m Problem
munify = fmap Unify

unify :: ProbId -> Equation -> Contextual ()
unify n q  = do
  --recordEqn q
  unify' n q
--unify n q
--  | trace ("Unifying " ++ show n ++ " " ++ pp q) False = error "unify"
  where
  unify' :: ProbId -> Equation -> Contextual ()
  unify' n q@(EQN (PI _A _B) f (PI _S _T) g pid) =
    do setProblem n
       x <- freshNom
       let ( xL, xR ) = (N (Var x TwinL) [], N (Var x TwinR) [])
       eq1 <-
         (munify (eqn (_B $$ xL)
                      (f $$ xL)
                      (_T $$ xR)
                      (g $$ xR)
                      (return $ CreatedBy (Ctx.infoRegion pid) n)))
       simplify n
                (Unify q)
                [Unify (EQN SET _A SET _S pid), allTwinsProb x _A _S eq1]
  unify' n q@(EQN (SIG _A _B) t (SIG _C _D) w pid) =
    do setProblem n
       a <- t %% Hd
       b <- t %% Tl
       c <- w %% Hd
       d <- w %% Tl
       eq1 <-
         munify (eqn (_B $$ a)
                     (return b)
                     (_D $$ c)
                     (return d)
                     (return $ CreatedBy (Ctx.infoRegion pid) n))
       simplify n
                (Unify q)
                [Unify (EQN _A a _C c pid), eq1]
    where
          -- >
  unify' n q@(EQN _ (N (Meta _) _) _ (N (Meta _) _) pid) =
    do
      setProblem n
      tryPrune n q $ tryPrune n (sym q) $ flexFlex n q
  -- >
  unify' n q@(EQN _ (N (Meta _) _) _ _ pid) =
    do
      setProblem n
      tryPrune n q $ flexRigid [] n q
  -- >
  unify' n q@(EQN _ _ _ (N (Meta _) _) pid) =
    do
      setProblem n
      tryPrune n (sym q) $ flexRigid [] n (sym q)
  -- >
  unify' n q@(EQN _ _ _ _ pid) =
    do
      setProblem n
      rigidRigid (CreatedBy (Ctx.infoRegion pid) n) q >>= simplify n (Unify q) . map Unify

-- Here |sym| swaps the two sides of an equation:
sym :: Equation -> Equation
sym (EQN _S s _T t pid) = EQN _T t _S s pid


-- \subsection{Rigid-rigid decomposition}
-- \label{subsec:impl:rigid-rigid}
-- A rigid-rigid equation (between two non-metavariable terms) can either
-- be decomposed into simpler equations or it is impossible to solve. For
-- example, $[[Pi A B == Pi S T]]$ splits into $[[A == S]], [[B == T]]$,
-- but $[[Pi A B == Sigma S T]]$ cannot be solved.
-- %% The |rigidRigid|
-- %% function implements the steps shown in Figure~\ref{fig:decompose}.
-- %% excluding the $\eta$-expansion steps, which are handled by |unify|
-- %% above.
rigidRigid :: EqnInfo -> Equation -> Contextual [Equation]
rigidRigid pid eqn =
  do
    retEqns <- rigidRigid' eqn
    --forM retEqns recordEqn --TODO only record in unify?
    return retEqns
    --TODO need derived edges?
  where
    rigidRigid' (EQN SET SET SET SET _) = return []
    -- >
    rigidRigid' (EQN SET (PI _A _B) SET (PI _S _T) _) =
      return [EQN SET _A SET _S pid
             ,EQN (_A --> SET)
                  _B
                  (_S --> SET)
                  _T pid]
    -- >
    rigidRigid' (EQN SET (SIG _A _B) SET (SIG _S _T) _) =
      return [EQN SET _A SET _S pid
             ,EQN (_A --> SET)
                  _B
                  (_S --> SET)
                  _T pid]
    -- >
    rigidRigid' (EQN _S (N (Var x w) ds) _T (N (Var y w') es) _)
      | x == y =
        do _X <- lookupVar x w
           _Y <- lookupVar y w'
           (EQN SET _X SET _Y pid :) <$>
             matchSpine pid _X
                        (N (Var x w) [])
                        ds
                        _Y
                        (N (Var y w') [])
                        es
    rigidRigid' (EQN SET Nat SET Nat _) = return []
    rigidRigid' (EQN SET (Fin n) SET (Fin n') _) = return [EQN Nat n Nat n' pid]
    rigidRigid' (EQN SET (Vec a m) SET (Vec b n) _) =
      return [EQN SET a SET b pid, EQN Nat m Nat n pid]
    --TODO need twins here?
    rigidRigid' (EQN SET (Eq a x y) SET (Eq a' x' y') _) =
      return [EQN SET a SET a' pid, EQN a x a' x' pid, EQN a y a' y' pid]
    rigidRigid' (EQN Nat Zero Nat Zero _) = return []
    rigidRigid' (EQN Nat (Succ m) Nat (Succ n) _) = return [EQN Nat m Nat n pid]
    rigidRigid' (EQN (Fin m) (FZero n) (Fin m') (FZero n') _) =
      return [EQN Nat n Nat n' pid, EQN Nat m Nat m' pid, EQN Nat m Nat n pid]
    --TODO need twins here?
    rigidRigid' (EQN (Fin m) (FSucc n f) (Fin m') (FSucc n' f') _) =
      return [EQN Nat n Nat n' pid
             ,EQN Nat m Nat m' pid
             ,EQN Nat m Nat n pid
             ,EQN (Fin n)
                  f
                  (Fin n)
                  f' pid]
    --TODO need to unify type indices of vectors?
    rigidRigid' (EQN (Vec a Zero) (VNil a') (Vec b Zero) (VNil b') _) =
      return [EQN SET a SET a' pid, EQN SET b SET b' pid, EQN SET a' SET b' pid]
    --TODO need to unify type indices of vectors?
    rigidRigid' (EQN (Vec a (Succ m)) (VCons a' (Succ m') h t) (Vec b (Succ n)) (VCons b' (Succ n') h' t') _) =
      return [EQN SET a SET a' pid
             ,EQN SET b SET b' pid
             ,EQN SET a' SET b' pid
             ,EQN Nat m Nat m' pid
             ,EQN Nat n Nat n' pid
             ,EQN Nat m' Nat n' pid
             ,EQN a h b h' pid
             ,EQN (Vec a m)
                  t
                  (Vec b n)
                  t' pid]
    rigidRigid' (EQN (Eq a x y) (ERefl a' z) (Eq b x' y') (ERefl b' z') _) =
      return [EQN SET a SET a' pid
             ,EQN SET b SET b' pid
             ,EQN SET a' SET b' pid
             ,EQN a x b x' pid
             ,EQN a y b y' pid
             ,EQN a x a' z pid
             ,EQN a y a' z pid
             ,EQN b x' b' z' pid
             ,EQN b y' b' z' pid
             ,EQN a' z b' z' pid]
    -- >
    --Anything can rigidly match with Bottom
    rigidRigid' (EQN _ (VBot _) _ _ _ ) = return []
    rigidRigid' (EQN _ _ _ (VBot _) _) = return []
    --Anything else, we should be able to catch in our type graph
    rigidRigid' eq@(EQN t1 v1 t2 v2 _) = return [] --badRigidRigid eq


-- badRigidRigid
--   :: Equation -> Contextual [Equation]
-- badRigidRigid (EQN t1 v1 t2 v2 _) =
--   throwError $
--   "Cannot rigidly match (" ++
--   prettyString v1 ++
--   " : " ++
--   prettyString t1 ++
--   ")  with (" ++ prettyString v2 ++ " : " ++ prettyString t2 ++ ")"

-- When we have the same rigid variable (or twins) at the head on both
-- sides, we proceed down the spine, demanding that projections are
-- identical and unifying terms in applications. Note that |matchSpine|
-- heterogeneously unfolds the types of the terms being applied to
-- determine the types of the arguments. For example, if
-- $[[x : Pi a : A . B a -> C]]$ then the constraint $[[x s t == x u v]]$
-- will decompose into
-- $[[(s : A) == (u : A) && (t : B s) == (v : B u)]]$.
matchSpine :: EqnInfo
           -> Type
           -> VAL
           -> [Elim]
           -> Type
           -> VAL
           -> [Elim]
           -> Contextual [Equation]
matchSpine pid (PI _A _B) u (A a:ds) (PI _S _T) v (A s:es) =
  (EQN _A a _S s pid :) <$> --TODO pid here?
  bind7 matchSpine (return pid)
        (_B $$ a)
        (u $$ a)
        (return ds)
        (_T $$ s)
        (v $$ s)
        (return es)
matchSpine pid (SIG _A _B) u (Hd:ds) (SIG _S _T) v (Hd:es) =
  bind7 matchSpine (return pid)
        (return _A)
        (u %% Hd)
        (return ds)
        (return _S)
        (v %% Hd)
        (return es)
matchSpine pid (SIG _A _B) u (Tl:ds) (SIG _S _T) v (Tl:es) =
  do a <- u %% Hd
     b <- u %% Tl
     s <- v %% Hd
     t <- v %% Tl
     bind7 matchSpine (return pid)
           (_B $$ a)
           (return b)
           (return ds)
           (_T $$ s)
           (return t)
           (return es)
--Match datatype eliminators
matchSpine pid Nat u (elim1@(NatElim m mz ms):ds) Nat v (elim2@(NatElim m' mz' ms'):es) =
  do let eq1 =
           EQN (Nat --> SET)
               m
               (Nat --> SET)
               m'
               pid
     eq2 <-
       eqn (m $$ Zero)
           (return mz)
           (m' $$ Zero)
           (return mz')
           (return pid)
     eq3 <-
       eqn (msVType m)
           (return ms)
           (msVType m')
           (return ms')
           (return pid)
     rest <-
       bind7 matchSpine (return pid)
             (m $$ u)
             (u %% elim1)
             (return ds)
             (m' $$ v)
             (v %% elim2)
             (return es)
     return $ [eq1, eq2, eq3] ++ rest
matchSpine pid (Fin ni) u (elim1@(FinElim m mz ms n):ds) (Fin ni') v (elim2@(FinElim m' mz' ms' n'):es) =
  do let eq1 =
           EQN (finmType)
               m
               (finmType)
               m' pid
     eq2 <-
       eqn (finmzVType m)
           (return mz)
           (finmzVType m')
           (return mz')
           (return pid)
     eq3 <-
       eqn (finmsVType m)
           (return ms)
           (finmsVType m')
           (return ms')
           (return pid)
     let eq4 = EQN (Nat) n Nat n' pid
     let eq5 = EQN (Nat) ni Nat ni' pid
     let eq6 = EQN (Nat) n Nat ni pid
     rest <-
       bind7 matchSpine (return pid)
             (m $$$ [n, u])
             (u %% elim1)
             (return ds)
             (m' $$$ [n', v])
             (v %% elim2)
             (return es)
     return $ [eq1, eq2, eq3, eq4, eq5, eq6] ++ rest
matchSpine pid (Vec a len) u (elim1@(VecElim b motive mn mc n):ds) (Vec a' len') v (elim2@(VecElim b' motive' mn' mc' n'):es) =
  do let eq1 = EQN SET a SET a' pid
     let eq2 = EQN SET b SET b' pid
     let eq3 = EQN SET a' SET b' pid
     let eq4 = EQN Nat len Nat len' pid
     let eq5 = EQN Nat len Nat n pid
     let eq6 = EQN Nat len' Nat n' pid
     eq7 <-
       eqn (vmVType b)
           (return motive)
           (vmVType b')
           (return motive')
           (return pid)
     eq8 <-
       eqn (mnVType b motive)
           (return mn)
           (mnVType b' motive')
           (return mn')
           (return pid)
     eq9 <-
       eqn (mcVType b motive)
           (return mc)
           (mcVType b' motive')
           (return mc')
           (return pid)
     let eq10 = EQN Nat n Nat n' pid
     rest <-
       bind7 matchSpine (return pid)
             (vResultVType motive n u)
             (u %% elim1)
             (return ds)
             (vResultVType motive' n' v)
             (v %% elim2)
             (return es)
     return $ [eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10] ++ rest
matchSpine pid (Eq a w x) u (elim1@(EqElim b m mr y z):ds) (Eq a' w' x') v (elim2@(EqElim b' m' mr' y' z'):es) =
  do let eq1 = EQN SET a SET a' pid
     let eq2 = EQN SET b SET b' pid
     let eq3 = EQN SET a' SET b' pid
     eq4 <-
       eqn (eqmVType b)
           (return m)
           (eqmVType b')
           (return m')
           (return pid)
     eq5 <-
       eqn (eqmrVType b m)
           (return mr)
           (eqmrVType b' m')
           (return mr')
           (return pid)
     let eq6 = EQN b y b' y' pid
     let eq7 = EQN b z b' z' pid
     rest <-
       bind7 matchSpine (return pid)
             (eqResultVType m y z u)
             (u %% elim1)
             (return ds)
             (eqResultVType m' y' z' v)
             (v %% elim2)
             (return es)
     return $ [eq1, eq2, eq3, eq4, eq5, eq6, eq7] ++ rest
matchSpine _ _ _ [] _ _ [] = return []
matchSpine _ t hd spn t' hd' spn' =
  throwError $
  "Cannot match (" ++
  (pp hd) ++
  " " ++
  (show $ map pp spn) ++
  ") :: " ++
  pp t ++
  "    with    (" ++
  (pp hd') ++ " " ++ (show $ map pp spn') ++ ") :: " ++ pp t'

-- \subsection{Flex-rigid equations}
-- \label{subsec:impl:flex-rigid}
-- A flex-rigid unification problem is one where one side is an applied
-- metavariable and the other is a non-metavariable term.  We move left
-- in the context, accumulating a list of metavariables that the term
-- depends on (the bracketed list of entries $[[XI]]$ in the rules).
-- Once we reach the target metavariable, we attempt to find a solution
-- by inversion.  This implements the steps in
-- Figure~\ref{fig:flex-rigid}, as described in
-- subsection~\ref{subsec:spec:flex-rigid}.
flexRigid
  :: [Entry] -> ProbId -> Equation -> Contextual ()
flexRigid _Xi n q@(EQN _ (N (Meta alpha) _) _ _ info) =
  setProblem n >>
  do _Gam <- ask
     popL >>=
       \e ->
         case e of
           E beta _T HOLE info
             | alpha == beta && alpha `elem` fmvs _Xi ->
               pushL e >> mapM_ pushL _Xi >> block n q
             | alpha == beta ->
               mapM_ pushL _Xi >> tryInvert n q _T (block n q >> pushL e)
             | beta `elem` fmvs (_Gam, _Xi, q) -> flexRigid (e : _Xi) n q
           _ -> pushR (Right e) >> flexRigid _Xi n q
-- %if False
flexRigid _ n q = throwError $ "flexRigid: " ++ show q

-- %endif
-- Given a flex-rigid or flex-flex equation whose head metavariable has
-- just been found in the context, the |tryInvert| control operator calls
-- |invert| to seek a solution to the equation. If it finds one, it
-- defines the metavariable and leaves the equation in the context (so
-- the definition will be substituted out and the equation found to be
-- reflexive by the constraint solver). If |invert| cannot find a
-- solution, it runs the continuation.
tryInvert
  :: ProbId -> Equation -> Type -> Contextual () -> Contextual ()
tryInvert n q@(EQN _ (N (Meta alpha) es) _ s info) _T k =
  setProblem n >>
  invert alpha _T es s >>=
  \m ->
    case m of
      Nothing -> k
      Just v -> active n q >> define (CreatedBy (Ctx.infoRegion info) n) [] alpha _T v
-- %if False
tryInvert _ _ q _ = throwError $ "tryInvert: " ++ show q

-- %endif
-- Given a metavariable $[[alpha]]$ of type $[[T]]$, spine
-- $[[</ ei // i/>]]$ and term $[[t]]$, |invert| attempts to find a value
-- for $[[alpha]]$ that solves the equation
-- $[[alpha </ ei // i /> == t]]$. It may also throw an error
-- if the problem is unsolvable due to an impossible (strong rigid)
-- occurrence.
invert
  :: Nom -> Type -> [Elim] -> VAL -> Contextual (Maybe VAL)
invert alpha _T es t =
  do let o =
           occurrence [alpha]
                      t
     when (isStrongRigid o) $ throwError "occurrence"
     case toVars es of
       Just xs
         | o == Nothing && linearOn t xs ->
           do flatTm <- flattenChoice $ lams xs t
              b <- localParams (const []) $ typecheck _T flatTm
              return $
                if b
                   then Just flatTm
                   else Nothing
       _ -> return Nothing

-- Here |toVars :: [Elim] -> Maybe [Nom]| tries to convert a spine to a
-- list of variables, and |linearOn :: VAL -> [Nom] -> Bool| determines
-- if a list of variables is linear on the free variables of a term. Note
-- that we typecheck the solution |lams xs t| under no parameters, so
-- typechecking will fail if an out-of-scope variable is used.
-- \subsection{Flex-flex equations}
-- \label{subsec:impl:flex-flex}
-- A flex-flex unification problem is one where both sides are applied
-- metavariables.  As in the flex-rigid case, we proceed leftwards
-- through the context, looking for one of the metavariables so we can
-- try to solve it with the other.  This implements the steps in
-- Figure~\ref{fig:flex-flex}, as described in
-- subsection~\ref{subsec:spec:flex-flex}.
flexFlex :: ProbId -> Equation -> Contextual ()
flexFlex n q@(EQN _ (N (Meta alpha) ds) _ (N (Meta beta) es) info) =
  setProblem n >>
  do _Gam <- ask
     popL >>=
       \e ->
         case e of
           E gamma _T HOLE _
             | gamma == alpha && gamma == beta ->
               block n q >> tryIntersect (CreatedBy (Ctx.infoRegion info) n) alpha _T ds es
             | gamma == alpha ->
               tryInvert n
                         q
                         _T
                         (flexRigid [e]
                                    n
                                    (sym q))
             | gamma == beta ->
               tryInvert n
                         (sym q)
                         _T
                         (flexRigid [e] n q)
             | gamma `elem` fmvs (_Gam, q) -> pushL e >> block n q
           _ -> pushR (Right e) >> flexFlex n q
-- %if False
flexFlex _ q = throwError $ "flexFlex: " ++ show q

-- %endif
-- %% Consider the case $[[alpha </ ei // i /> == beta </ xj // j />]]$
-- %% where $[[</ xj // j />]]$ is a list of variables but
-- %% $[[</ ei // i />]]$ is not.  If we reach $[[alpha]]$ first then we
-- %% might get stuck even if we could potentially solve for
-- %% $[[beta]]$.  This would be correct if order were important in the
-- %% metacontext, for example if we wanted to implement let-generalisation
-- %% \citep{gundry2010}. Here it is not, so we can simply pick up
-- %% $[[alpha]]$ and carry on moving left.
-- When we have a flex-flex equation with the same metavariable on both
-- sides, $[[alpha </ xi // i /> == alpha </ yi // i />]]$, where
-- $[[</ xi // i />]]$ and $[[</ yi // i />]]$ are both lists of
-- variables, we can solve the equation by restricting $[[alpha]]$ to the
-- arguments on which $[[</ xi // i />]]$ and $[[</ yi // i />]]$ agree
-- (i.e. creating a new metavariable $[[beta]]$ and using it to solve
-- $[[alpha]]$). The |tryIntersect| control operator tests if both spines are
-- lists of variables, then calls |intersect| to generate a restricted
-- type for the metavariable. If this succeeds, it creates a new
-- metavariable and solves the old one. Otherwise, it leaves the old
-- metavariable in the context.
tryIntersect
  :: EqnInfo -> Nom -> Type -> [Elim] -> [Elim] -> Contextual ()
tryIntersect pid alpha _T ds es =
  case (toVars ds, toVars es) of
    ( Just xs, Just ys ) ->
      intersect [] [] _T xs ys >>=
      \m ->
        case m of --TODO intersect creator?
          Just ( _U, f ) -> hole pid [] _U $ \beta -> define pid [] alpha _T (f beta)
          Nothing -> pushL (E alpha _T HOLE pid)
    _ -> pushL (E alpha _T HOLE pid)

-- Given the type of $[[alpha]]$ and the two spines, |intersect| produces
-- a type for $[[beta]]$ and a term with which to solve $[[alpha]]$ given
-- $[[beta]]$. It accumulates lists of the original and retained
-- parameters (|_Phi| and |_Psi| respectively).
intersect ::
          [( Nom, Type )]
          -> [( Nom, Type )]
          -> Type
          -> [Nom]
          -> [Nom]
          -> Contextual (Maybe ( Type, VAL -> VAL ))
intersect _Phi _Psi _S [] []
  | (Set.fromList $ fvs _S) `isSubsetOf` (Set.fromList $ vars _Psi) =
    return $
    Just (_Pis _Psi _S, \beta -> lams' _Phi (runFreshM $ beta $*$ _Psi))
  | otherwise = return Nothing
intersect _Phi _Psi (PI _A _B) (x:xs) (y:ys) =
  do z <- freshNom
     let _Psi' =
           _Psi ++
           if x == y
              then [(z, _A)]
              else []
     ourApp <- (_B $$ var z)
     intersect (_Phi ++ [(z, _A)]) _Psi' ourApp xs ys
-- %if False
intersect _ _ _ _ _ = throwError "intersect: ill-typed!"

-- %endif
-- Note that we have to generate fresh names in case the renamings are
-- not linear. Also note that the resulting type is well-formed: if the
-- domain of a $\Pi$ depends on a previous variable that was removed,
-- then the renamings will not agree, so it will be removed as well.
-- \subsection{Pruning}
-- \label{subsec:impl:pruning}
-- When we have a flex-rigid or flex-flex equation, we might be able to
-- make some progress by pruning the metavariables contained within it,
-- as described in Figure~\ref{fig:pruning} and
-- subsection~\ref{subsec:spec:pruning}.  The |tryPrune| control operator calls
-- |prune|, and if it learns anything from pruning, leaves the current
-- problem where it is and instantiates the pruned metavariable.  If not,
-- it runs the continuation.
tryPrune
  :: ProbId -> Equation -> Contextual () -> Contextual ()
--tryPrune n q@(EQN _ (N (Meta _) ds) _ t) k
--  | trace ("TryPrune " ++ show n ++ " " ++ pp q) False = error "tryPrune"
tryPrune n q@(EQN _ (N (Meta _) ds) _ t info) k =
  --trace ("tryPrune " ++ show n ++ ", " ++ pp q) $
  setProblem n >>
  do _Gam <- ask
     let potentials = vars _Gam
         freesToIgnore   --trace ("Pruning " ++ (show potentials) ++ " from " ++ (show $ map pp ds) ++ " ignoring " ++ (show $ fvs ds) ++ "\n   in exp " ++ pp t)  $
            =
           fvs ds
     u <- prune (potentials \\ freesToIgnore) t
     --trace ("Prune result " ++ show u) $
     case u of
       d:_ -> active n q >> instantiate (CreatedBy (Ctx.infoRegion info) n) d
       [] -> k
-- %if False
tryPrune n q _ = do
  setProblem n
  throwError $ "tryPrune: " ++ show q

-- %endif
-- Pruning a term requires traversing it looking for occurrences of
-- forbidden variables. If any occur rigidly, the corresponding
-- constraint is impossible. On the other hand, if we encounter a
-- metavariable, we observe that it cannot depend on any arguments that
-- contain rigid occurrences of forbidden variables. This can be
-- implemented by replacing it with a fresh variable of restricted type.
-- The |prune| function generates a list of triples |(beta, _U, f)| where
-- |beta| is a metavariable, |_U| is a type for a new metavariable
-- |gamma| and |f gamma| is a solution for |beta|. We maintain the
-- invariant that |_U| and |f gamma| depend only on metavariables defined
-- prior to |beta| in the context.
prune
  :: [Nom] -> VAL -> Contextual [( Nom, Type, VAL -> VAL )]
--prune xs t | trace ("In Pruning " ++ (show xs) ++ " from " ++ pp t) False = error "prune"
prune xs SET = return []
prune xs (VChoice s t) = (++) <$> prune xs s <*> prune xs t
prune xs Nat = return []
prune xs (Fin n) = prune xs n
prune xs (Vec a n) = (++) <$> prune xs a <*> prune xs n
prune xs (Eq a x y) =
  (\x y z -> x ++ y ++ z) <$> prune xs a <*> prune xs x <*> prune xs y
prune xs Zero = return []
prune xs (Succ n) = prune xs n
prune xs (FZero n) = prune xs n
prune xs (FSucc n f) = (++) <$> prune xs n <*> prune xs f
prune xs (VNil a) = prune xs a
prune xs (VCons a n h t) =
  (\x y z m -> x ++ y ++ z ++ m) <$> prune xs a <*> prune xs h <*> prune xs t <*>
  prune xs n
prune xs (ERefl a x) = (++) <$> prune xs a <*> prune xs x
prune xs (PI _S _T) = (++) <$> prune xs _S <*> prune xs _T
prune xs (SIG _S _T) = (++) <$> prune xs _S <*> prune xs _T
prune xs (PAIR s t) = (++) <$> prune xs s <*> prune xs t
prune xs (L b) = prune xs =<< (snd <$> unbind b)
prune xs neut@(N (Var z _) es)
  | z `elem` xs =
    throwError $
    "Pruning overlap: Cannot prune " ++
    (show xs) ++ " from neutral " ++ (pp neut)
  | otherwise = concat <$> mapM pruneElim es
  where pruneElim (A a) = prune xs a
        pruneElim _ = return []
prune xs (N (Meta beta) es) =
  do _T <- lookupMeta beta
     maybe [] (\( _U, f ) -> [(beta, _U, f)]) <$> pruneSpine [] [] xs _T es
-- %if False
prune xs (C _ ts) = throwError "concat <$> mapM (prune xs) ts"

-- %endif
-- Once a metavariable has been found, |pruneSpine| unfolds its type and
-- inspects its arguments, generating lists of unpruned and pruned
-- arguments (|_Phi| and |_Psi|).  If an argument contains a rigid
-- occurrence of a forbidden variable, or its type rigidly depends on a
-- previously removed argument, then it is removed.  Ultimately, it
-- generates a simplified type for the metavariable if the codomain type
-- does not depend on a pruned argument.
pruneSpine
  :: [( Nom, Type )]
  -> [( Nom, Type )]
  -> [Nom]
  -> Type
  -> [Elim]
  -> Contextual (Maybe ( Type, VAL -> VAL ))
pruneSpine _Phi _Psi xs (PI _A _B) (A a:es)
  | not stuck =
    do z <- freshNom
       let _Psi' =
             _Psi ++
             if pruned
                then []
                else [(z, _A)]
       ourApp <- (_B $$ var z)
       pruneSpine (_Phi ++ [(z, _A)])
                  _Psi'
                  xs
                  ourApp
                  es
  | otherwise = return Nothing
  where o = occurrence xs a
        o' =
          occurrence (vars _Phi \\ vars _Psi)
                     _A
        pruned = isRigid o || isRigid o'
        stuck =
          isFlexible o ||
          (isNothing o && isFlexible o') || (not pruned && not (isVar a))
pruneSpine _Phi _Psi _ _T []
  | (Set.fromList $ fvs _T) `isSubsetOf` (Set.fromList $ vars _Psi) &&
      _Phi /= _Psi =
    return $ Just (_Pis _Psi _T, \v -> lams' _Phi (runFreshM $ v $*$ _Psi))
pruneSpine _ _ _ _ _ = return Nothing

-- After pruning, we can |instantiate| a pruned metavariable by moving
-- left through the context until we find the relevant metavariable, then
-- creating a new metavariable and solving the old one.
instantiate
  :: EqnInfo -> ( Nom, Type, VAL -> VAL ) -> Contextual ()
instantiate pid d@( alpha, _T, f ) =
  popL >>=
  \e ->
    case e of
      E beta _U HOLE pid
        | alpha == beta -> hole pid [] _T $ \t -> define pid [] beta _U (f t)
      _ -> pushR (Right e) >> instantiate pid d

-- \subsection{Metavariable and problem simplification}
-- \label{subsec:impl:simplification}
-- Given a problem, the |solver| simplifies it according to the rules in
-- Figure~\ref{fig:solve}, introduces parameters and calls |unify| from
-- subsection~\ref{subsec:impl:unification}.  In particular, it removes
-- $\Sigma$-types from parameters, potentially eliminating projections,
-- and replaces twins whose types are definitionally equal with a normal
-- parameter.
solver :: ProbId -> Problem -> Contextual ()
--solver n prob | trace ("solver " ++ show [show n, pp prob]) False = error "solver"
solver n p@(Unify q) =
  Ctx.recordProblem (Ctx.DerivedEqn n p) n p >>
  setProblem n >>
  isReflexive q >>=
  \b ->
    if b
       then solved n q
       else unify n q `catchError` failed n q
solver n prob@(All p b) =
  --Ctx.recordProblem n prob >> --TODO only record innermost?
  setProblem n >>
  do ( x, q ) <- unbind b
     --trace ("Solver forall unbind " ++ show (x,q)) $
     case p of
       _
         | x `notElem` fvs q ->
           simplify n
                    (All p b)
                    [q]
       P _S ->
         splitSig [] x _S >>=
         \m ->
           case m of
             Just ( y, _A, z, _B, s, _ ) ->
               solver n (allProb y _A (allProb z _B (subst x s q)))
             Nothing -> localParams (++ [(x, P _S)]) $ solver n q
       Twins _S _T ->
         equal SET _S _T >>=
         \c ->
           if c
              then solver n (allProb x _S (subst x (var x) q))
              else localParams (++ [(x, Twins _S _T)]) $ solver n q

-- \newpage
-- Given the name and type of a metavariable, |lower| attempts to
-- simplify it by removing $\Sigma$-types, according to the metavariable
-- simplification rules in Figure~\ref{fig:solve}. If it cannot be
-- simplified, it appends it to the (left) context.
--TODO lower for elim cases?
lower
  :: EqnInfo -> [( Nom, Type )] -> Nom -> Type -> Contextual ()
lower pid _Phi alpha (SIG _S _T) =
  hole pid _Phi _S $
  \s ->
    bind4 hole (return pid)
          (return _Phi)
          (_T $$ s) $
    return $
    \t ->
      define pid _Phi
             alpha
             (SIG _S _T)
             (PAIR s t)
-- >
lower pid _Phi alpha (PI _S _T) =
  do x <- freshNom
     ourApp1 <- (_T $$ var x)
     splitSig [] x _S >>=
       maybe (lower pid (_Phi ++ [(x, _S)]) alpha ourApp1)
             (\( y, _A, z, _B, s, ( u, v ) ) ->
                do ourApp2 <- (_T $$ s)
                   hole pid _Phi (_Pi y _A (_Pi z _B ourApp2)) $
                     \w ->
                       do ourApp3 <- (w $$$ [u, v])
                          define pid _Phi
                                 alpha
                                 (PI _S _T)
                                 (lam x ourApp3))
lower pid _Phi alpha _T = pushL (E alpha (_Pis _Phi _T) HOLE pid)

-- Both |solver| and |lower| above need to split $\Sigma$-types (possibly
-- underneath a bunch of parameters) into their components.  For example,
-- $[[y : Pi x : X . Sigma S T]]$ splits into $[[y0 : Pi x : X . S]]$ and
-- $[[y1 : Pi x : X . T (y0 x)]]$.  Given the name of a variable and its
-- type, |splitSig| attempts to split it, returning fresh variables for
-- the two components of the $\Sigma$-type, an inhabitant of the original
-- type in terms of the new variables and inhabitants of the new types by
-- projecting the original variable.
splitSig
  :: Fresh m
  => [( Nom, Type )]
  -> Nom
  -> Type
  -> m (Maybe ( Nom, Type, Nom, Type, VAL, ( VAL, VAL ) ))
splitSig _Phi x (SIG _S _T) =
  do y <- freshNom
     z <- freshNom
     ourApp1 <- (_T $$ var y)
     ourApp2 <- (var z $*$ _Phi)
     ourApp3 <- (var y $*$ _Phi)
     ourApp4 <- ((%% Hd) =<< var x $*$ _Phi)
     ourApp5 <- ((%% Tl) =<< var x $*$ _Phi)
     return $
       Just (y
            ,_Pis _Phi _S
            ,z
            ,_Pis _Phi ourApp1
            ,lams' _Phi (PAIR ourApp3 ourApp2)
            ,(lams' _Phi ourApp4, lams' _Phi ourApp5))
splitSig _Phi x (PI _A _B) =
  do a <- freshNom
     ourApp <- (_B $$ var a)
     splitSig (_Phi ++ [(a, _A)]) x ourApp
splitSig _ _ _ = return Nothing

-- \subsection{Solvitur ambulando}
-- \label{subsec:impl:ambulando}
-- We organise constraint solving via an automaton that lazily propagates
-- a substitution rightwards through the metacontext, making progress on
-- active problems and maintaining the invariant that the entries to the
-- left include no active problems. This is not the only possible
-- strategy: indeed, it is crucial for guaranteeing most general
-- solutions that solving the constraints in any order would produce the
-- same result.
-- A problem may be in any of five possible states: |Active| and ready to
-- be worked on; |Blocked| and unable to make progress in its current
-- state; |Pending| the solution of some other problems in order to
-- become solved itself; |Solved| as it has become reflexive; or |Failed|
-- because it is unsolvable. The specification simply removes constraints
-- that are pending or solved, and represents failed constraints as
-- failure of the whole process, but in practice it is often useful to have a
-- more fine-grained representation.
-- < data ProblemState  =  Active  |  Blocked  |  Pending [ProbId]
-- <                               |  Solved   |  Failed String
-- In the interests of simplicity, |Blocked| problems do not store any
-- information about when they may be resumed, and applying a
-- substitution that modifies them in any way makes them |Active|. A
-- useful optimisation would be to track the conditions under which they
-- should become active, typically when particular metavariables are
-- solved or types become definitionally equal.
-- The |ambulando| automaton carries a list of problems that have been
-- solved, for updating the state of subsequent problems, and a
-- substitution with definitions for metavariables.
ambulando :: [ProbId] -> Subs -> Contextual ()
ambulando ns theta =
  popR >>=
  \x ->
    case x of
      -- if right context is empty, stop
      Nothing                   --Make sure our final substitutions are applied
       ->
        do Ctx.modifyLM (mapM (update [] theta))
           return ()
      -- compose suspended substitutions
      Just (Left theta') -> ambulando ns (compSubs theta theta')
      -- process entries
      Just (Right e) -> do
        updateVal <- update ns theta e
        case updateVal of
          Prob n p Active ->
            pushR (Left theta) >> solver n p >> ambulando ns Map.empty
          Prob n p Solved ->
            pushL (Prob n p Solved) >> ambulando (n : ns) theta
          E alpha _T HOLE info -> lower info [] alpha _T >> ambulando ns theta
          e' -> pushL e' >> ambulando ns theta

-- Given a list of solved problems, a substitution and an entry, |update|
-- returns a modified entry with the substitution applied and the problem
-- state changed if appropriate.
update :: [ProbId] -> Subs -> Entry -> Contextual Entry
--update ns theta entry | trace ("UPDATE " ++ show ns ++ " " ++ show theta ++ " " ++ pp entry) False = error "update"
update pids subs e = do
  let newE = update' pids subs e
  --Record our substitutions, letting us get rid of function applications
  Ctx.recordEntrySub e newE
  return newE
  where
    update' :: [ProbId] -> Subs -> Entry -> Entry
    update' _ theta (Prob n p Blocked) = Prob n p' k
      where p' = substs (Map.toList theta) p
            k =
              if p == p'
                 then Blocked
                 else Active
    update' ns theta (Prob n p (Pending ys))
      | null rs = Prob n p' Solved
      | otherwise = Prob n p' (Pending rs)
      where rs = ys \\ ns
            p' = substs (Map.toList theta) p
    update' _ _ e'@(Prob _ _ Solved) = e'
    update' _ _ e'@(Prob _ _ (Failed _)) = e'
    update' _ theta e' =
      --trace ("UPDATE SUBS"  ++ pp e' ++ "\n   " ++ show theta ++ "\n\n") $
      substs (Map.toList theta)
             e'
