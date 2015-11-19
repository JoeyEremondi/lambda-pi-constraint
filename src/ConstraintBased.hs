
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
            ty <- freshType
            ty `evaluatesTo` cEval_ tyt (fst g, [])
            cType_ ii g e ty
            return ty
iType_ ii g Star_
   =  return conStar
iType_ ii g (Pi_ tyt tyt')
   =  do  cType_ ii g tyt conStar
          ty <- freshType
          ty `evaluatesTo` cEval_ tyt (fst g, [])
          cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)
                    (cSubst_ 0 (Free_ (Local ii)) tyt') conStar
          return conStar
iType_ ii g (Free_ x)
  =     case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  unknownIdent (render (iPrint_ 0 0 (Free_ x)))
iType_ ii g (e1 :$: e2)
  =     do  si <- iType_ ii g e1
            case si of
              VPi_  ty ty'  ->  do  cType_ ii g e2 ty
                                    return ( ty' (cEval_ e2 (fst g, [])))
              _                  ->  throwError "illegal application"

iType_ ii g Nat_                  =  return conStar
iType_ ii g (NatElim_ m mz ms n)  =
  do  cType_ ii g m (contype $ VPi_ VNat_ (const VStar_))
      let mVal  = cEval_ m (fst g, [])
      cType_ ii g mz (contype $ mVal `vapp_` VZero_)
      cType_ ii g ms (VPi_ VNat_ (\ k -> VPi_ (mVal `vapp_` k) (\ _ -> mVal `vapp_` VSucc_ k)))
      cType_ ii g n VNat_
      let nVal = cEval_ n (fst g, [])
      return (mVal `vapp_` nVal)

iType_ ii g (Vec_ a n) =
  do  cType_ ii g a  VStar_
      cType_ ii g n  VNat_
      return VStar_
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
      aVal <- freshType
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
            tyAnnot <- freshType
            tyAnnot `evaluatesTo` cEval_ (Inf_ e) (fst g, []) --TODO is this right?
cType_ ii g (Lam_ e) fnTy = do
    argTy <- freshType
    returnTy <- freshType
    unify fnTy (mkPi argTy returnTy) --TODO fix this
    cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, argTy ) : g))) g)
                (cSubst_ 0 (Free_ (Local ii)) e) ( _returnTy (vfree_ (Local ii)))

cType_ ii g Zero_      ty  =  unify ty (contype VNat_)
cType_ ii g (Succ_ k)  ty  = do
  unify ty (contype VNat_)
  cType_ ii g k (contype VNat_)

cType_ ii g (Nil_ a) ty =
  do
      bVal <- freshType
      unify ty (VVec_ bVal VZero_)
      cType_ ii g a conStar
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
cType_ ii g (Cons_ a n x xs) (VVec_ bVal (VSucc_ k)) =
  do  cType_ ii g a conStar
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
      cType_ ii g n VNat_
      let nVal = cEval_ n (fst g, [])
      unless  (quote0_ nVal == quote0_ k)
              (throwError "number mismatch")
      cType_ ii g x aVal
      cType_ ii g xs (VVec_ bVal k)

cType_ ii g (Refl_ a z) (VEq_ bVal xVal yVal) =
  do  cType_ ii g a VStar_
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
      cType_ ii g z aVal
      let zVal = cEval_ z (fst g, [])
      unless  (quote0_ zVal == quote0_ xVal && quote0_ zVal == quote0_ yVal)
              (throwError "type mismatch")
