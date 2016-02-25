
module ConstraintBased (checker) where

import Prelude hiding (print)

import Data.Char
import Data.List

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

import Text.ParserCombinators.Parsec hiding (State, parse)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token

import System.Console.Readline
import System.IO hiding (print)

import System.IO.Error

import Control.Applicative

import Common

import Constraint

import qualified PatternUnify.Tm as Tm

import PatternUnify.Test (prettyString)

import Debug.Trace (trace)

--import qualified Solver

mapSnd f (a,b) = (a, f b)

splitContext :: [(Name, a)] -> ([(String, a)], [(Int, a)])
splitContext entries = helper entries [] []
  where
    helper [] globals locals = (globals, locals)
    helper ( (Global s, x) : rest) globals locals =
      helper rest ((s,x) : globals) locals
    helper ((Local i, x) : rest) globals locals =
      helper rest globals ((i,x) : locals)

checker :: TypeChecker
checker (nameEnv, context) term = do
  let (typeGlobals, typeLocals) = splitContext $ map (mapSnd $ vToUnifForm 0) context
  let (valGlobals, valLocals) = splitContext $ map (mapSnd $ vToUnifForm 0) nameEnv
  let finalVar =  getConstraints (WholeEnv valLocals typeLocals valGlobals typeGlobals) term
  unifToValue <$> solveConstraintM finalVar


conStar = Tm.SET

getConstraints :: WholeEnv -> ITerm_ -> ConstraintM Tm.Nom
getConstraints env term = do
  finalType <- iType0_ env term
  finalVar <- freshTopLevel Tm.SET
  unifySets startRegion finalType (Tm.meta finalVar) env
  return finalVar

iType0_ :: WholeEnv -> ITerm_ -> ConstraintM ConType
iType0_ = iType_ 0

iType_ :: Int -> WholeEnv -> ITerm_ -> ConstraintM ConType
iType_ iiGlobal g (L region it) = trace ("ITYPE" ++ show it ++ "\nenv: " ++ show g) $
  iType_' iiGlobal g it
  where
    iType_' ii g m@(Meta_ s) = do
      metaType <- freshType g
      let ourNom = metaNom s
      --Add metavariable to our context
      declareMeta ourNom metaType
      return metaType

    iType_' ii g (Ann_ e tyt )
      =
        do
          cType_  ii g tyt conStar
          ty <- evaluate tyt g
          --trace ("&&" ++ show ii ++ "Annotated " ++ show tyt ++ " as " ++ prettyString ty ++ "\nenv: " ++ show g) $
          cType_ ii g e ty
          return ty
    iType_' ii g Star_
       =  return conStar
    iType_' ii g (Pi_ tyt tyt')
       =  do  cType_ ii g tyt conStar
              let argNom = localName (ii+1)
              ty <- evaluate tyt g --Ensure LHS has type Set
              --Ensure, when we apply free var to RHS, we get a set
              let newEnv = (addType (ii, ty)  g)
              cType_  (ii + 1) newEnv
                        (cSubst_ 0 (builtin $ Free_ (Local ii)) tyt') conStar
              return conStar
    iType_' ii g (Free_ x)
      =     case typeLookup x g of
              Just ty        ->  return ty
              Nothing        ->  unknownIdent g (render (iPrint_ 0 0 (builtin $ Free_ x)))
    iType_' ii g (e1 :$: e2)
      =     do
                fnType <- iType_ ii g e1
                piArg <- freshType g
                piBodyFn <- fresh g (piArg Tm.--> Tm.SET) --TODO star to star?
                unifySets region (fnType) (Tm.PI piArg piBodyFn) g

                --Ensure that the argument has the proper type
                cType_ ii g e2 piArg

                --Get a type for the evaluation of the argument
                argVal <- evaluate e2 g

                --Our resulting type is the application of our arg type into the
                --body of the pi type
                return $ piBodyFn Tm.$$ argVal

    iType_' ii g Nat_                  =  return conStar
    iType_' ii g (NatElim_ m mz ms n)  =
      do  cType_ ii g m (Tm.Nat Tm.--> Tm.SET)
          --evaluate $ our param m
          mVal <- evaluate m g
          --Check that mz has type (m 0)
          cType_ ii g mz (mVal Tm.$$ Tm.Zero)
          --Check that ms has type ( (k: N) -> m k -> m (S k) )
          let recPiType =
                mkPiFn Tm.Nat $ \k -> mkPiFn (mVal Tm.$$ k)
                  ( \_ -> mVal Tm.$$ (Tm.Succ k) )
          cType_ ii g ms recPiType
          --Make sure the number param is a nat
          cType_ ii g n Tm.Nat

          --We infer that our final expression has type (m n)
          nVal <- evaluate n g
          return $ mVal Tm.$$ nVal

    iType_' ii g (Vec_ a n) =
      do  cType_ ii g a  conStar
          cType_ ii g n  Tm.Nat
          return conStar
    iType_' ii g (VecElim_ a m mn mc n vs) =

      do  cType_ ii g a conStar
          aVal <- evaluate a g
          cType_ ii g m
            (  mkPiFn Tm.Nat ( \n -> mkPiFn  (Tm.Vec aVal n) ( \ _ -> conStar)))
          mVal <- evaluate m g
          cType_ ii g mn (foldl (Tm.$$) mVal [ Tm.Zero, Tm.VNil aVal ])
          cType_ ii g mc
            (  mkPiFn Tm.Nat ( \ n ->
               mkPiFn aVal ( \ y ->
               mkPiFn ( Tm.Vec aVal n) ( \ ys ->
               mkPiFn (foldl (Tm.$$) mVal  [n, ys]) ( \ _ ->
               (foldl (Tm.$$) mVal [(Tm.Succ n), Tm.VCons aVal n y ys]))))))
          cType_ ii g n $ Tm.Nat
          nVal <- evaluate n g
          cType_ ii g vs ((Tm.Vec aVal nVal ))
          vsVal <- evaluate vs g
          return (foldl (Tm.$$) mVal [nVal, vsVal])


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
            (mkPiFn aVal (\ x ->
             mkPiFn aVal ( \ y ->
             mkPiFn ((  Tm.Eq aVal x y)) ( \ _ -> conStar))))
          --evaluate $ our given m value
          mVal <- evaluate m g
          cType_ i g mr
            (mkPiFn aVal ( \ x ->
             ( foldl (Tm.$$) mVal $ [x, x] )))
          cType_ i g x aVal
          xVal <- evaluate x g
          cType_ i g y aVal
          yVal <- evaluate y g
          --TODO make this nicer with a fold?
          let
            eqC =
              ((Tm.Eq yVal xVal aVal))
          cType_ i g eq eqC
          eqVal <- evaluate eq g
          return (foldl (Tm.$$) mVal [xVal, yVal])

    iType_' ii g (Bound_ vi) = error "TODO why never bound?"
      --return $ (snd $ snd g `listLookup` (ii - (vi+1) ) ) --TODO is this right?


cType_ :: Int -> WholeEnv -> CTerm_ -> ConType -> ConstraintM ()
cType_ iiGlobal g (L region ct) = trace ("CTYPE" ++ show ct) $
  cType_' iiGlobal g ct
  where
    cType_' ii g (Inf_ e) tyAnnot
          =
            do
              tyInferred <- iType_ ii g e
              --Ensure that the annotation type and our inferred type unify
              --We have to evaluate $ our normal form
              --trace ("INF " ++ show e ++ "\nunifying " ++ show [tyAnnot, tyInferred] ++ "\nenv " ++ show g) $
              unifySets region tyAnnot tyInferred g
    {-
    --Default: can't fully infer function types? --TODO
    cType_' ii g (Lam_ body) (Tm.PI argTy returnTy) = do
      let newEnv = addType (ii, argTy ) g
          arg = builtin $ Free_ (Local ii)
          subbedBody = cSubst_ 0 arg body
          argVal = Tm.var $ localName (ii)
      cType_  (ii + 1) newEnv subbedBody (returnTy Tm.$$ argVal)
    --TODO is this okay? Fns should always be fully annotated?
    -}

    --Special case when we have metavariable in type
    cType_' ii g (Lam_ body) fnTy = do
        argTy <- freshType g
        --Our return type should be a function, from input type to set
        let newEnv = trace ("Lambda newEnv " ++ show ii ++ " old " ++ show g) $ addType (ii, argTy ) g
        returnTyFn <- fresh g (argTy Tm.--> conStar)
        let arg = trace ("Lambda giving arg " ++ show ii) $ builtin $ Free_ (Local ii)
        let argName = localName (ii) --TODO ii or 0?
        let argVal = Tm.var argName --iToUnifForm ii newEnv arg
        unifySets region fnTy (Tm.PI argTy returnTyFn)  g
        returnTy <- freshType newEnv
        unifySets region returnTy (returnTyFn Tm.$$ argVal) newEnv
        --unify  returnTyFn (Tm.lam argName returnTy) (argTy Tm.--> conStar) g --TODO is argVal good?
        --Convert bound instances of our variable into free ones
        let subbedBody = cSubst_ 0 arg body
        cType_  (ii + 1) newEnv subbedBody returnTy



    cType_' ii g Zero_      ty  =  unifySets region ty Tm.Nat g
    cType_' ii g (Succ_ k)  ty  = do
      unifySets region ty Tm.Nat g
      cType_ ii g k Tm.Nat

    cType_' ii g (Nil_ a) ty =
      do
          bVal <- freshType g
          unifySets region ty (mkVec bVal Tm.Zero) g
          cType_ ii g a conStar
          aVal <- evaluate a g
          unifySets region aVal bVal g
    cType_' ii g (Cons_ a n x xs) ty  =
      do  bVal <- freshType g
          k <- fresh g Tm.Nat
          --Trickery to get a Type_ to a ConType
          let kVal = Tm.Succ k
          unifySets region ty (mkVec bVal kVal) g
          cType_ ii g a conStar

          aVal <- evaluate a g
          unifySets region aVal bVal g

          cType_ ii g n Tm.Nat

          --Make sure our numbers match
          nVal <- evaluate n g
          unify region nVal kVal Tm.Nat g

          --Make sure our new head has the right list type
          cType_ ii g x aVal
          --Make sure our tail has the right length
          cType_ ii g xs (mkVec bVal k)

    cType_' ii g (Refl_ a z) ty =
      do  bVal <- freshType g
          xVal <- fresh g bVal
          yVal <- fresh g bVal
          unifySets region ty (mkEq bVal xVal yVal) g
          --Check that our type argument has kind *
          cType_ ii g a conStar
          --Get evaluation constraint for our type argument
          aVal <- evaluate a g

          --Check that our given type is the same as our inferred type --TODO is this right?
          unifySets region aVal bVal g

          --Check that the value we're proving on has type A
          cType_ ii g z aVal

          --evaluate $ the value that we're proving equality on
          zVal <- evaluate z g

          --Show constraint that the type parameters must match that type
          unify region zVal xVal bVal g
          unify region zVal yVal bVal g
          --TODO something special for quoting
