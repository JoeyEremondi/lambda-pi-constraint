
module ConstraintBased (checker) where

import Prelude hiding (print)

import Data.List
import Data.Char

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language

import System.Console.Readline
import System.IO hiding (print)

import System.IO.Error

import Common

import Constraint

import qualified PatternUnify.Tm as Tm

--import qualified Solver


checker :: TypeChecker
checker (nameEnv, context) term = error "TODO checker" {- do
  let newContext = map (\(a,b) -> (a, cToUnifForm0 b) ) context
  let checkResults = Solver.solveConstraints $ getConstraints (nameEnv, newContext) term
  case (Solver.finalResults checkResults) of
    Solver.Err s -> error s
    Solver.Defer -> error "Should never have defer at end!"
    Solver.Ok t -> return t -}


conStar = Tm.SET

getConstraints env term = do
  finalType <- iType0_ env term
  finalVar <- freshVar
  return (finalType, finalVar)

iType0_ :: (NameEnv Value_, ConstrContext) -> ITerm_ -> ConstraintM cToUnifForm0
iType0_ = iType_ 0

iType_ :: Int -> (NameEnv Value_, ConstrContext) -> ITerm_ -> ConstraintM cToUnifForm0
iType_ ii g (L region it) = iType_' ii g it
  where
    iType_' ii g (Ann_ e tyt )
      =     do  cType_  ii g tyt conStar
                ty <- evaluate tyt g
                cType_ ii g e ty
                return ty
    iType_' ii g Star_
       =  return conStar
    iType_' ii g (Pi_ tyt tyt')
       =  do  cType_ ii g tyt conStar
              ty <- evaluate tyt g
              cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)
                        (cSubst_ 0 (builtin $ Free_ (Local ii)) tyt') conStar
              return conStar
    iType_' ii g (Free_ x)
      =     case lookup x (snd g) of
              Just ty        ->  return ty
              Nothing        ->  unknownIdent (render (iPrint_ 0 0 (builtin $ Free_ x)))
    iType_' ii g (e1 :$: e2)
      =     do
                fnType <- iType_ ii g e1
                piArg <- fresh
                piBody <- fresh
                unify (fnType) (Tm.PI piArg piBody) g

                --Ensure that the argument has the proper type
                cType_ ii g e2 piArg

                --Get a type for the evaluation of the argument
                argVal <- evaluate e2 g

                --Our resulting type is the application of our arg type into the
                --body of the pi type
                return $ (Tm.$$) piBody argVal

    iType_' ii g Nat_                  =  return conStar
    iType_' ii g (NatElim_ m mz ms n)  =
      do  cType_ ii g m (cToUnifForm0 $ VPi_ VNat_ (const VStar_))
          --evaluate $ our param m
          mVal <- evaluate m g
          --Check that mz has type (m 0)
          cType_ ii g mz (mVal Tm.$$ (cToUnifForm0 VZero_))
          --Check that ms has type ( (k: N) -> m k -> m (S k) )
          let recPiType =
                Tm.PI (cToUnifForm0 VNat_) $ conTyFn $ \k -> Tm.PI (mVal Tm.$$ cToUnifForm0 k)
                  (conTyFn $ \_ -> mVal Tm.$$ (cToUnifForm0 $ VSucc_ k) )
          cType_ ii g ms recPiType
          --Make sure the number param is a nat
          cType_ ii g n (cToUnifForm0 VNat_)

          --We infer that our final expression has type (m n)
          nVal <- evaluate n g
          return $ mVal Tm.$$ nVal

    iType_' ii g (Vec_ a n) =
      do  cType_ ii g a  conStar
          cType_ ii g n  (cToUnifForm0 VNat_)
          return conStar
    iType_' ii g (VecElim_ a m mn mc n vs) =

      do  cType_ ii g a conStar
          aVal <- evaluate a g
          cType_ ii g m
            (  Tm.PI (cToUnifForm0 VNat_) (conTyFn $ \n -> Tm.PI ((Tm.$$) (conTyFn $ \av -> cToUnifForm0 $ VVec_ av n) aVal) (conTyFn $ \ _ -> conStar)))
          mVal <- evaluate m g
          cType_ ii g mn (foldl applyVal mVal [cToUnifForm0 VZero_, (liftConTyFn $ \av -> VNil_ av ) Tm.$$ aVal])
          cType_ ii g mc
            (  Tm.PI (cToUnifForm0 VNat_) (conTyFn $ \ n ->
               Tm.PI aVal (conTyFn $ \ y ->
               Tm.PI ( (liftConTyFn $ \av -> VVec_ av n) Tm.$$ aVal) (conTyFn $ \ ys ->
               Tm.PI (foldl applyVal mVal $ map cToUnifForm0 [n, ys]) (conTyFn $ \ _ ->
               (foldl applyVal mVal [cToUnifForm0 (VSucc_ n), (liftConTyFn $ \av -> VCons_ av n y ys) Tm.$$ aVal]))))))
          cType_ ii g n $ cToUnifForm0 VNat_
          nVal <- evaluate n g
          cType_ ii g vs ((conTyFn $ \av -> (liftConTyFn $ \nv -> VVec_ av nv ) Tm.$$ aVal) Tm.$$ nVal)
          vsVal <- evaluate vs g
          return (foldl applyVal mVal [nVal, vsVal])


    iType_' i g (Eq_ a x y) =
      do  cType_ i g a conStar
          aVal <- evaluate a g
          cType_ i g x aVal
          cType_ i g y aVal
          return conStar
    iType_' i g (EqElim_ a m mr x y eq) =
      do
          --Our a value should be a type
          cType_ i g a conStar
          --evaluate $ our a value
          aVal <- evaluate a g
          cType_ i g m
            (Tm.PI aVal (conTyFn $ \ x ->
             Tm.PI aVal (conTyFn $ \ y ->
             Tm.PI ((conTyFn $ \av -> cToUnifForm0 $ VEq_ av x y) Tm.$$ aVal) (conTyFn $ \ _ -> conStar))))
          --evaluate $ our given m value
          mVal <- evaluate m g
          cType_ i g mr
            (Tm.PI aVal (conTyFn $ \ x ->
             ( foldl applyVal mVal $ map cToUnifForm0 [x, x] )))
          cType_ i g x aVal
          xVal <- evaluate x g
          cType_ i g y aVal
          yVal <- evaluate y g
          --TODO make this nicer with a fold?
          let
            eqC =
              (conTyFn $ \a -> (conTyFn $ \b -> (conTyFn $ \c -> cToUnifForm0 (VEq_ a b c)) Tm.$$ yVal) Tm.$$ xVal ) Tm.$$ aVal
          cType_ i g eq eqC
          eqVal <- evaluate eq g
          return (foldl applyVal mVal [xVal, yVal])

    iType_' i g (Bound_ vi) = error "TODO why never bound?"


cType_ :: Int -> (NameEnv Value_,ConstrContext) -> CTerm_ -> cToUnifForm0 -> ConstraintM ()
cType_ ii g (L region ct) = cType_' ii g ct
  where
    cType_' ii g (Inf_ e) tyAnnot
          =
            do
              tyInferred <- iType_ ii g e
              --Ensure that the annotation type and our inferred type unify
              --We have to evaluate $ our normal form
              unify tyAnnot tyInferred g


    cType_' ii g (Lam_ e) fnTy = do
        argTy <- fresh
        returnTyFn <- fresh
        unify fnTy (Tm.PI argTy returnTyFn) g --TODO fix this
        let returnTy = (Tm.$$) returnTyFn $ cToUnifForm0 (vfree_ (Local ii))
        let subbedBody = cSubst_ 0 (builtin $ Free_ (Local ii)) e
        cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, argTy ) : g))) g) subbedBody returnTy
        --TODO better name?



    cType_' ii g Zero_      ty  =  unify ty (cToUnifForm0 VNat_) g
    cType_' ii g (Succ_ k)  ty  = do
      unify ty (cToUnifForm0 VNat_) g
      cType_ ii g k (cToUnifForm0 VNat_)

    cType_' ii g (Nil_ a) ty =
      do
          bVal <- fresh
          unify ty (mkVec bVal $ cToUnifForm0 VZero_) g
          cType_ ii g a conStar
          aVal <- evaluate a g
          unify aVal bVal g
    cType_' ii g (Cons_ a n x xs) ty  =
      do  bVal <- fresh
          k <- (fresh :: ConstraintM cToUnifForm0)
          --Trickery to get a Type_ to a cToUnifForm0
          let kVal = (Tm.$$) (liftConTyFn (\val -> VSucc_ val) ) k
          unify ty (mkVec bVal kVal) g
          cType_ ii g a conStar

          aVal <- evaluate a g
          unify aVal bVal g

          cType_ ii g n (cToUnifForm0 VNat_)

          --Make sure our numbers match
          nVal <- evaluate n g
          unify nVal kVal g

          --Make sure our new head has the right list type
          cType_ ii g x aVal
          --Make sure our tail has the right length
          cType_ ii g xs (mkVec bVal k)

    cType_' ii g (Refl_ a z) ty =
      do  bVal <- fresh
          xVal <- fresh
          yVal <- fresh
          unify ty (mkEq bVal xVal yVal) g
          --Check that our type argument has kind *
          cType_ ii g a conStar
          --Get evaluation constraint for our type argument
          aVal <- evaluate a g

          --Check that our given type is the same as our inferred type --TODO is this right?
          unify aVal bVal g

          --Check that the value we're proving on has type A
          cType_ ii g z aVal

          --evaluate $ the value that we're proving equality on
          zVal <- evaluate z g

          --Show constraint that the type parameters must match that type
          unify zVal xVal g
          unify zVal yVal g
          --TODO something special for quoting
