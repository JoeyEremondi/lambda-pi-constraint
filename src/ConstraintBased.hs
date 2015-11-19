
module ConstraintBased (checker) where

import Prelude hiding (print)

import Control.Monad.Error
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

catch = catchIOError

checker :: TypeChecker
checker = error "TODO implement"

conStar = contype VStar_

type ConstrContext = [(Name, ConType)]

iType0_ :: (NameEnv Value_, ConstrContext) -> ITerm_ -> ConstraintM ConType
iType0_ = iType_ 0

iType_ :: Int -> (NameEnv Value_, ConstrContext) -> ITerm_ -> ConstraintM ConType
iType_ ii g (Ann_ e tyt )
  =     do  cType_  ii g tyt conStar
            ty <- fresh
            ty `evaluatesTo` cEval_ tyt (fst g, [])
            cType_ ii g e ty
            return ty
iType_ ii g Star_
   =  return conStar
iType_ ii g (Pi_ tyt tyt')
   =  do  cType_ ii g tyt conStar
          ty <- fresh
          ty `evaluatesTo` cEval_ tyt (fst g, [])
          cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)
                    (cSubst_ 0 (Free_ (Local ii)) tyt') conStar
          return conStar
iType_ ii g (Free_ x)
  =     case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  unknownIdent (render (iPrint_ 0 0 (Free_ x)))
iType_ ii g (e1 :$: e2)
  =     do
            fnType <- iType_ ii g e1
            piArg <- fresh
            piBody <- fresh
            unify (fnType) (mkPi piArg piBody)

            --Ensure that the argument has the proper type
            cType_ ii g e2 piArg

            --Get a type for the evaluation of the argument
            argVal <- fresh
            argVal `evaluatesTo` (cEval_ e2 (fst g, []))

            --Our resulting type is the application of our arg type into the
            --body of the pi type
            return $ applyPi piBody piArg

iType_ ii g Nat_                  =  return conStar
iType_ ii g (NatElim_ m mz ms n)  =
  do  cType_ ii g m (contype $ VPi_ VNat_ (const VStar_))

      --Evaluate our param m
      mVal <- fresh
      mVal `evaluatesTo` cEval_ m (fst g, [])

      mvalAppK <- fresh
      (mVal, contype VZero_) `vappIs` mvalAppK
      cType_ ii g mz mvalAppK
      cType_ ii g ms $
         (mkPi (contype VNat_)
            $ TyFn (\ k -> VPi_ mvalAppK (\ _ -> mVal `vapp_` VSucc_ k)))
      --Make sure the number param is a nat
      cType_ ii g n (contype VNat_)
      let nVal = cEval_ n (fst g, [])
      return (mVal `vapp_` nVal)

iType_ ii g (Vec_ a n) =
  do  cType_ ii g a  conStar
      cType_ ii g n  (contype VNat_)
      return conStar
iType_ ii g (VecElim_ a m mn mc n vs) =
  do  cType_ ii g a VStar_
      let aVal = cEval_ a (fst g, [])
      cType_ ii g m
        (  VPi_ VNat_ (\n -> VPi_ (VVec_ aVal n) (\ _ -> VStar_)))
      let mVal = cEval_ m (fst g, [])
      cType_ ii g mn (foldl vapp_ mVal [VZero_, VNil_ aVal])
      cType_ ii g mc
        (  VPi_ VNat_ (\ n ->
           VPi_ aVal (\ y ->
           VPi_ (VVec_ aVal n) (\ ys ->
           VPi_ (foldl vapp_ mVal [n, ys]) (\ _ ->
           (foldl vapp_ mVal [VSucc_ n, VCons_ aVal n y ys]))))))
      cType_ ii g n VNat_
      let nVal = cEval_ n (fst g, [])
      cType_ ii g vs (VVec_ aVal nVal)
      let vsVal = cEval_ vs (fst g, [])
      return (foldl vapp_ mVal [nVal, vsVal])

iType_ i g (Eq_ a x y) =
  do  cType_ i g a conStar
      aVal <- fresh
      aVal `evaluatesTo` cEval_ a (fst g, [])
      cType_ i g x aVal
      cType_ i g y aVal
      return conStar
iType_ i g (EqElim_ a m mr x y eq) =
  do  cType_ i g a conStar
      let aVal = cEval_ a (fst g, [])
      cType_ i g m
        (VPi_ aVal (\ x ->
         VPi_ aVal (\ y ->
         VPi_ (VEq_ aVal x y) (\ _ -> VStar_))))
      let mVal = cEval_ m (fst g, [])
      cType_ i g mr
        (VPi_ aVal (\ x ->
         foldl vapp_ mVal [x, x]))
      cType_ i g x aVal
      let xVal = cEval_ x (fst g, [])
      cType_ i g y aVal
      let yVal = cEval_ y (fst g, [])
      cType_ i g eq (VEq_ aVal xVal yVal)
      let eqVal = cEval_ eq (fst g, [])
      return (foldl vapp_ mVal [xVal, yVal])



cType_ :: Int -> (NameEnv Value_,ConstrContext) -> CTerm_ -> ConType -> ConstraintM ()
cType_ ii g (Inf_ e) v
  =     do  tyInferred <- iType_ ii g e
            --Ensure that the annotation type and our inferred type unify
            --We have to evaluate our normal form
            tyAnnot <- fresh
            tyAnnot `evaluatesTo` cEval_ (Inf_ e) (fst g, []) --TODO is this right?


cType_ ii g (Lam_ e) fnTy = do
    argTy <- fresh
    returnTyFn <- fresh
    unify fnTy (mkPi argTy returnTyFn) --TODO fix this
    let returnTy = applyPi returnTyFn $ contype (vfree_ (Local ii))
    let subbedBody = cSubst_ 0 (Free_ (Local ii)) e
    cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, argTy ) : g))) g) subbedBody returnTy
    --TODO better name?



cType_ ii g Zero_      ty  =  unify ty (contype VNat_)
cType_ ii g (Succ_ k)  ty  = do
  unify ty (contype VNat_)
  cType_ ii g k (contype VNat_)

cType_ ii g (Nil_ a) ty =
  do
      bVal <- fresh
      unify ty (mkVec bVal $ contype VZero_)
      cType_ ii g a conStar
      aVal <- fresh
      aVal `evaluatesTo` cEval_ a (fst g, [])
      unify aVal bVal
cType_ ii g (Cons_ a n x xs) ty  =
  do  bVal <- fresh
      k <- (fresh :: ConstraintM ConType)
      --Trickery to get a Type_ to a ConType
      let kVal = applyPi (TyFn (\val -> VSucc_ val) ) k
      unify ty (mkVec bVal kVal)
      cType_ ii g a conStar

      aVal <- fresh
      aVal `evaluatesTo` cEval_ a (fst g, [])
      unify aVal bVal

      cType_ ii g n (contype VNat_)

      --Make sure our numbers match
      nVal <- fresh
      nVal `evaluatesTo` cEval_ n (fst g, [])
      unify nVal kVal

      --Make sure our new head has the right list type
      cType_ ii g x aVal
      --Make sure our tail has the right length
      cType_ ii g xs (mkVec bVal k)

cType_ ii g (Refl_ a z) ty =
  do  bVal <- fresh
      xVal <- fresh
      yVal <- fresh
      unify ty (mkEq bVal xVal yVal)
      --Check that our type argument has kind *
      cType_ ii g a conStar
      --Get evaluation constraint for our type argument
      aVal <- fresh
      aVal `evaluatesTo` cEval_ a (fst g, [])

      --Check that our given type is the same as our inferred type --TODO is this right?
      unify aVal bVal

      --Check that the value we're proving on has type A
      cType_ ii g z aVal

      --Evaluate the value that we're proving equality on
      zVal <- fresh
      zVal `evaluatesTo` cEval_ z (fst g, [])

      --Show constraint that the type parameters must match that type
      unify zVal xVal
      unify zVal yVal
      --TODO something special for quoting
