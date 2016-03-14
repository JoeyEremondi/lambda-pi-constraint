
module ConstraintBased (checker) where

import Prelude hiding (print)

import Data.Char
import Data.List

import Text.PrettyPrint.HughesPJ hiding (parens, ($$))
import qualified Text.PrettyPrint.HughesPJ as PP

import Text.ParserCombinators.Parsec hiding (State, parse)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token

import qualified Unbound.LocallyNameless as LN


import System.Console.Readline
import System.IO hiding (print)

import System.IO.Error

import Control.Applicative

import Common

import Constraint hiding (cToUnifForm, iToUnifForm)

import qualified Data.List as List

import qualified PatternUnify.Tm as Tm

import Data.Foldable (foldlM, foldrM)


import Debug.Trace (trace)

--import qualified Solver

mapSnd f (a,b) = (a, f b)
mapFst f (a,b) = (f a, b)


errorMsg :: [(Region, String)] -> String
errorMsg pairs =
  List.intercalate "\n" $
  map (\(reg, err) -> show reg ++ ": " ++ err ) pairs

checker :: TypeChecker
checker (nameEnv, context) term =
  let
    (typeGlobals, typeLocals) = splitContext context
    (valGlobals, valLocals) = splitContext  nameEnv
    finalVar =  getConstraints (WholeEnv valLocals typeLocals valGlobals typeGlobals) term
    soln = solveConstraintM finalVar
    solvedMetas = snd <$> soln
    solvedString = case solvedMetas of
      Left _ -> ""
      Right pairs ->
        "Solved metas:\n"
        ++ (intercalate "\n" (map (\(s, v) -> s ++ " := " ++ Tm.prettyString v) pairs))
    eitherVal = trace solvedString $ fst <$> soln
  in
    case eitherVal of
      Left pairs -> Left $ errorMsg pairs
      Right x -> Right x


conStar = Tm.SET

getConstraints :: WholeEnv -> ITerm_ -> ConstraintM Tm.Nom
--getConstraints env term | trace ("\n\n**************************************\nChecking, converted " ++ show (iPrint_ 0 0 term))  $ trace ("\n  into " ++ Tm.prettyString (constrEval (map (mapFst Global) $ globalTypes env, map (mapFst Global) $ globalValues env) term ) ++ "\n\n") False
--  = error "genConstraints"
getConstraints env term =
  do
    finalType <- iType0_ env term
    finalVar <- freshTopLevel Tm.SET
    unifySets startRegion finalType (Tm.meta finalVar) env
    return finalVar

iType0_ :: WholeEnv -> ITerm_ -> ConstraintM ConType
iType0_ = iType_ 0

iType_ :: Int -> WholeEnv -> ITerm_ -> ConstraintM ConType
iType_ iiGlobal g lit@(L reg it) = --trace ("ITYPE " ++ show (iPrint_ 0 0 lit)) $
  iType_' iiGlobal g it
  where
    iType_' ii g m@(Meta_ s) = do
      metaType <- freshType reg g
      let ourNom = metaNom s
      recordSourceMeta s
      --Add metavariable to our context
      declareMeta ourNom metaType
      return metaType

    iType_' ii g (Ann_ e tyt )
      =
        do
          cType_  ii g tyt conStar
          ty <- evaluate ii tyt g
          --trace ("&&" ++ show ii ++ "Annotated " ++ show e ++ " as " ++ show ty)  $
          cType_ ii g e ty
          return ty
    iType_' ii g Star_
       =  return conStar
    iType_' ii g (Pi_ tyt tyt')
       =  do  cType_ ii g tyt conStar
              argNom <- freshNom $ localName (ii)
              ty <- evaluate ii tyt g --Ensure LHS has type Set
              --Ensure, when we apply free var to RHS, we get a set
              let newEnv = addType (ii, ty) $ addValue (ii, Tm.var argNom)  g
              cType_  (ii + 1) newEnv
                        (cSubst_ 0 (builtin $ Free_ (Local ii)) tyt') conStar
              return conStar
    iType_' ii g (Free_ x)
      =     case typeLookup x g of
              Just ty        ->  return ty
              Nothing        ->  unknownIdent reg g (render (iPrint_ 0 0 (builtin $ Free_ x)))
    iType_' ii g (funExp :$: argExp)
      =     do
                fnType <- iType_ ii g funExp
                piArg <- freshType (region argExp) g
                piBodyFn <- fresh (region funExp) g (piArg Tm.--> Tm.SET) --TODO star to star?
                unifySets reg (fnType) (Tm.PI piArg piBodyFn) g

                --Ensure that the argument has the proper type
                cType_ ii g argExp piArg

                --Get a type for the evaluation of the argument
                argVal <- evaluate ii argExp g

                --Our resulting type is the application of our arg type into the
                --body of the pi type
                piBodyFn Tm.$$ argVal

    iType_' ii g Nat_                  =  return conStar
    iType_' ii g (NatElim_ m mz ms n)  =
      do  cType_ ii g m (Tm.Nat Tm.--> Tm.SET)
          --evaluate ii $ our param m
          mVal <- evaluate ii m g
          --Check that mz has type (m 0)
          ourApp1 <- (mVal Tm.$$ Tm.Zero)
          cType_ ii g mz ourApp1
          --Check that ms has type ( (k: N) -> m k -> m (S k) )
          let ln = LN.s2n "l"
          let lv = Tm.var ln
          ourApp2 <- (Tm.msVType mVal)
          cType_ ii g ms ourApp2
          --Make sure the number param is a nat
          cType_ ii g n Tm.Nat

          --We infer that our final expression has type (m n)
          nVal <- evaluate ii n g
          mVal Tm.$$ nVal

    iType_' ii g (Fin_ n) = do
      cType_ ii g n Tm.Nat
      return Tm.SET

    iType_' ii g (FinElim_ m mz ms n f) = do
      mVal <- evaluate ii m g
      --mzVal <- evaluate ii m g
      --msVal <- evaluate ii m g
      nVal <- evaluate ii n g
      fVal <- evaluate ii f g
      cType_ ii g m (Tm.finmType)
      cType_ ii g mz =<< (Tm.finmzVType mVal)
      cType_ ii g ms =<< (Tm.finmsVType mVal)
      cType_ ii g n (Tm.Nat)
      cType_ ii g f (Tm.Fin nVal)
      mVal Tm.$$$ [nVal, fVal]

    iType_' ii g (Vec_ a n) =
      do  cType_ ii g a  conStar
          cType_ ii g n  Tm.Nat
          return conStar
    iType_' ii g (VecElim_ a m mn mc n vs) =

      do  cType_ ii g a conStar
          aVal <- evaluate ii a g
          cType_ ii g m
            (  mkPiFn Tm.Nat ( \n -> mkPiFn  (Tm.Vec aVal n) ( \ _ -> conStar)))
          mVal <- evaluate ii m g
          cType_ ii g mn =<< (foldlM (Tm.$$) mVal [ Tm.Zero, Tm.VNil aVal ])
          cType_ ii g mc =<<
            (  mkPiFnM Tm.Nat ( \ n ->
               mkPiFnM aVal ( \ y ->
               mkPiFnM ( Tm.Vec aVal n) ( \ ys -> do
                 mnys <- (mVal Tm.$$$  [n, ys])
                 mkPiFnM mnys  ( \ _ ->
                  (mVal Tm.$$$ [(Tm.Succ n), Tm.VCons aVal n y ys]))))))
          cType_ ii g n $ Tm.Nat
          nVal <- evaluate ii n g
          cType_ ii g vs ((Tm.Vec aVal nVal ))
          vsVal <- evaluate ii vs g
          (mVal Tm.$$$ [nVal, vsVal])


    iType_' ii g (Eq_ a x y) =
      do  cType_ ii g a conStar
          aVal <- evaluate ii a g
          cType_ ii g x aVal
          cType_ ii g y aVal
          return conStar
    iType_' ii g (EqElim_ a m mr x y eq) =
      do
          --Our a value should be a type
          cType_ ii g a conStar
          --evaluate ii $ our a value
          aVal <- evaluate ii a g
          cType_ ii g m
            (mkPiFn aVal (\ x ->
             mkPiFn aVal ( \ y ->
             mkPiFn ((  Tm.Eq aVal x y)) ( \ _ -> conStar))))
          --evaluate ii $ our given m value
          mVal <- evaluate ii m g
          cType_ ii g mr =<<
            (mkPiFnM aVal ( \ x ->
             (  mVal Tm.$$$ [x, x] )))
          cType_ ii g x aVal
          xVal <- evaluate ii x g
          cType_ ii g y aVal
          yVal <- evaluate ii y g
          --TODO make this nicer with a fold?
          let
            eqC =
              ((Tm.Eq yVal xVal aVal))
          cType_ ii g eq eqC
          eqVal <- evaluate ii eq g
          (mVal Tm.$$$ [xVal, yVal])

    iType_' ii g (Bound_ vi) = error "TODO why never bound?"
      --return $ (snd $ snd g `listLookup` (ii - (vi+1) ) ) --TODO is this right?


cType_ :: Int -> WholeEnv -> CTerm_ -> ConType -> ConstraintM ()
cType_ iiGlobal g lct@(L reg ct) globalTy = --trace ("CTYPE " ++ show (cPrint_ 0 0 lct) ++ " :: " ++ Tm.prettyString globalTy) $
  cType_' iiGlobal g ct globalTy
  where
    cType_' ii g (Inf_ e) tyAnnot
          =
            do
              tyInferred <- iType_ ii g e
              --Ensure that the annotation type and our inferred type unify
              --We have to evaluate ii $ our normal form
              --trace ("INF " ++ show e ++ "\nunifying " ++ show [tyAnnot, tyInferred] ++ "\nenv " ++ show g) $
              unifySets reg tyAnnot tyInferred g
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
        argTy <- freshType reg g
        argName <- freshNom $ localName (ii) --TODO ii or 0?
        --Our return type should be a function, from input type to set
        let newEnv = -- trace ("Lambda newEnv " ++ show ii ++ " old " ++ show g) $
              addValue (ii, Tm.var argName) $ addType (ii, argTy ) g
        returnTyFn <- fresh (region body) g (argTy Tm.--> conStar)
        let arg = -- trace ("Lambda giving arg " ++ show ii) $
              builtin $ Free_ (Local ii)
            --TODO g or newEnv?
        argVal <-evalInEnv g $ Tm.var argName --iToUnifForm ii newEnv arg
        unifySets reg fnTy (Tm.PI argTy returnTyFn)  g
        returnTy <- freshType (region body) newEnv
        appedTy <- (returnTyFn Tm.$$ argVal)
        unifySets reg returnTy appedTy newEnv
        --unify  returnTyFn (Tm.lam argName returnTy) (argTy Tm.--> conStar) g --TODO is argVal good?
        --Convert bound instances of our variable into free ones
        let subbedBody = cSubst_ 0 arg body
        cType_  (ii + 1) newEnv subbedBody returnTy



    cType_' ii g Zero_      ty  =  unifySets reg ty Tm.Nat g
    cType_' ii g (Succ_ k)  ty  = do
      unifySets reg ty Tm.Nat g
      cType_ ii g k Tm.Nat

    cType_' ii g (FZero_ f)      ty  =  do
      cType_ ii g f Tm.Nat
      fVal <- evaluate ii f g
      unifySets reg ty (Tm.Fin fVal) g
    cType_' ii g (FSucc_ k f)  ty  = do
      cType_ ii g f Tm.Nat
      fVal <- evaluate ii f g
      unifySets reg ty (Tm.Fin fVal) g
      cType_ ii g k Tm.Nat

    cType_' ii g (Nil_ a) ty =
      do
          bVal <- freshType reg g
          unifySets reg ty (mkVec bVal Tm.Zero) g
          cType_ ii g a conStar
          aVal <- evaluate ii a g
          unifySets reg aVal bVal g
    cType_' ii g (Cons_ a n x xs) ty  =
      do  bVal <- freshType (region a) g
          k <- fresh (region n) g Tm.Nat
          --Trickery to get a Type_ to a ConType
          let kVal = Tm.Succ k
          unifySets reg ty (mkVec bVal kVal) g
          cType_ ii g a conStar

          aVal <- evaluate ii a g
          unifySets reg aVal bVal g

          cType_ ii g n Tm.Nat

          --Make sure our numbers match
          nVal <- evaluate ii n g
          unify reg nVal kVal Tm.Nat g

          --Make sure our new head has the right list type
          cType_ ii g x aVal
          --Make sure our tail has the right length
          cType_ ii g xs (mkVec bVal k)

    cType_' ii g (Refl_ a z) ty =
      do  bVal <- freshType (region a) g
          xVal <- fresh (region z) g bVal
          yVal <- fresh (region z) g bVal
          unifySets reg ty (mkEq bVal xVal yVal) g
          --Check that our type argument has kind *
          cType_ ii g a conStar
          --Get evaluation constraint for our type argument
          aVal <- evaluate ii a g

          --Check that our given type is the same as our inferred type --TODO is this right?
          unifySets reg aVal bVal g

          --Check that the value we're proving on has type A
          cType_ ii g z aVal

          --evaluate ii $ the value that we're proving equality on
          zVal <- evaluate ii z g

          --Show constraint that the type parameters must match that type
          unify reg zVal xVal bVal g
          unify reg zVal yVal bVal g
          --TODO something special for quoting
