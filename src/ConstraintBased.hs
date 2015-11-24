
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

import qualified Solver
--import Debug.Trace (trace)


checker :: TypeChecker
checker (nameEnv, context) term = trace ("Checking term\n" ++ show term ++ "\n\n") $ do
  let newContext = map (\(a,b) -> (a, conType b) ) context
  let checkResults = Solver.solveConstraints $ getConstraints (nameEnv, newContext) term
  case (Solver.finalResults checkResults) of
    Solver.Err s -> error s
    Solver.Defer -> error "Should never have defer at end!"
    Solver.Ok t -> return t

conStar = conType VStar_

getConstraints env term = do
  finalType <- iType0_ env term
  finalVar <- freshVar
  return (finalType, finalVar)

iType0_ :: (NameEnv Value_, ConstrContext) -> ITerm_ -> ConstraintM ConType
iType0_ = iType_ 0

iType_ :: Int -> (NameEnv Value_, ConstrContext) -> ITerm_ -> ConstraintM ConType
iType_ ii g (Ann_ e tyt )
  =     do  cType_  ii g tyt conStar
            ty <- evaluate tyt g
            cType_ ii g e ty
            return ty
iType_ ii g Star_
   =  return conStar
iType_ ii g (Pi_ tyt tyt')
   =  do  cType_ ii g tyt conStar
          ty <- evaluate tyt g
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
            unify (fnType) (mkPi piArg piBody) g

            --Ensure that the argument has the proper type
            cType_ ii g e2 piArg

            --Get a type for the evaluation of the argument
            argVal <- evaluate e2 g

            --Our resulting type is the application of our arg type into the
            --body of the pi type
            return $ applyPi piBody argVal

iType_ ii g Nat_                  =  return conStar
iType_ ii g (NatElim_ m mz ms n)  = trace "NatElim case" $
  do  cType_ ii g m (conType $ VPi_ VNat_ (const VStar_))
      --evaluate $ our param m
      mVal <- evaluate m g
      --Check that mz has type (m 0)
      cType_ ii g mz (mVal `applyVal` (conType VZero_))
      --Check that ms has type ( (k: N) -> m k -> m (S k) )
      let recPiType =
            mkPi (conType VNat_) $ conTyFn $ \k -> mkPi (mVal `applyVal` conType k)
              (conTyFn $ \_ -> mVal `applyVal` (conType $ VSucc_ k) )
      cType_ ii g ms recPiType
      --Make sure the number param is a nat
      cType_ ii g n (conType VNat_)

      --We infer that our final expression has type (m n)
      nVal <- evaluate n g
      return $ mVal `applyVal` nVal

iType_ ii g (Vec_ a n) =
  do  cType_ ii g a  conStar
      cType_ ii g n  (conType VNat_)
      return conStar
iType_ ii g (VecElim_ a m mn mc n vs) =

  do  cType_ ii g a conStar
      aVal <- evaluate a g
      cType_ ii g m
        (  mkPi (conType VNat_) (conTyFn $ \n -> mkPi (applyPi (conTyFn $ \av -> conType $ VVec_ av n) aVal) (conTyFn $ \ _ -> conStar)))
      mVal <- evaluate m g
      cType_ ii g mn (foldl applyVal mVal [conType VZero_, (liftConTyFn $ \av -> VNil_ av ) `applyPi` aVal])
      cType_ ii g mc
        (  mkPi (conType VNat_) (conTyFn $ \ n ->
           mkPi aVal (conTyFn $ \ y ->
           mkPi ( (liftConTyFn $ \av -> VVec_ av n) `applyPi` aVal) (conTyFn $ \ ys ->
           mkPi (foldl applyVal mVal $ map conType [n, ys]) (conTyFn $ \ _ ->
           (foldl applyVal mVal [conType (VSucc_ n), (liftConTyFn $ \av -> VCons_ av n y ys) `applyPi` aVal]))))))
      cType_ ii g n $ conType VNat_
      nVal <- evaluate n g
      cType_ ii g vs ((conTyFn $ \av -> (liftConTyFn $ \nv -> VVec_ av nv ) `applyPi` aVal) `applyPi` nVal)
      vsVal <- evaluate vs g
      return (foldl applyVal mVal [nVal, vsVal])


iType_ i g (Eq_ a x y) =
  do  cType_ i g a conStar
      aVal <- evaluate a g
      cType_ i g x aVal
      cType_ i g y aVal
      return conStar
iType_ i g (EqElim_ a m mr x y eq) =
  do
      --Our a value should be a type
      cType_ i g a conStar
      --evaluate $ our a value
      aVal <- evaluate a g
      cType_ i g m
        (mkPi aVal (conTyFn $ \ x ->
         mkPi aVal (conTyFn $ \ y ->
         mkPi ((conTyFn $ \av -> conType $ VEq_ av x y) `applyPi` aVal) (conTyFn $ \ _ -> conStar))))
      --evaluate $ our given m value
      mVal <- evaluate m g
      cType_ i g mr
        (mkPi aVal (conTyFn $ \ x ->
         ( foldl applyVal mVal $ map conType [x, x] )))
      cType_ i g x aVal
      xVal <- evaluate x g
      cType_ i g y aVal
      yVal <- evaluate y g
      --TODO make this nicer with a fold?
      let
        eqC =
          (conTyFn $ \a -> (conTyFn $ \b -> (conTyFn $ \c -> conType (VEq_ a b c)) `applyPi` yVal) `applyPi` xVal ) `applyPi` aVal
      cType_ i g eq eqC
      eqVal <- evaluate eq g
      return (foldl applyVal mVal [xVal, yVal])

iType_ i g (Bound_ vi) = error "TODO why never bound?"


cType_ :: Int -> (NameEnv Value_,ConstrContext) -> CTerm_ -> ConType -> ConstraintM ()
cType_ ii g (Inf_ e) tyAnnot
  =
    do
      tyInferred <- iType_ ii g e
      --Ensure that the annotation type and our inferred type unify
      --We have to evaluate $ our normal form
      unify tyAnnot tyInferred g


cType_ ii g (Lam_ e) fnTy = do
    argTy <- fresh
    returnTyFn <- fresh
    unify fnTy (mkPi argTy returnTyFn) g --TODO fix this
    let returnTy = applyPi returnTyFn $ conType (vfree_ (Local ii))
    let subbedBody = cSubst_ 0 (Free_ (Local ii)) e
    cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, argTy ) : g))) g) subbedBody returnTy
    --TODO better name?



cType_ ii g Zero_      ty  =  unify ty (conType VNat_) g
cType_ ii g (Succ_ k)  ty  = do
  unify ty (conType VNat_) g
  cType_ ii g k (conType VNat_)

cType_ ii g (Nil_ a) ty =
  do
      bVal <- fresh
      unify ty (mkVec bVal $ conType VZero_) g
      cType_ ii g a conStar
      aVal <- evaluate a g
      unify aVal bVal g
cType_ ii g (Cons_ a n x xs) ty  =
  do  bVal <- fresh
      k <- (fresh :: ConstraintM ConType)
      --Trickery to get a Type_ to a ConType
      let kVal = applyPi (liftConTyFn (\val -> VSucc_ val) ) k
      unify ty (mkVec bVal kVal) g
      cType_ ii g a conStar

      aVal <- evaluate a g
      unify aVal bVal g

      cType_ ii g n (conType VNat_)

      --Make sure our numbers match
      nVal <- evaluate n g
      unify nVal kVal g

      --Make sure our new head has the right list type
      cType_ ii g x aVal
      --Make sure our tail has the right length
      cType_ ii g xs (mkVec bVal k)

cType_ ii g (Refl_ a z) ty =
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
