
module ConstraintBased (checker) where

import Prelude hiding (print)

--import Data.List

import qualified Data.Map as Map

import qualified Data.Maybe as Maybe

import Text.PrettyPrint.HughesPJ hiding (parens, ($$))

import qualified Unbound.Generics.LocallyNameless as LN

import Common

import Constraint hiding (cToUnifForm, iToUnifForm)

import qualified Data.List as List

import PatternUnify.SolverConfig
import qualified PatternUnify.Tm as Tm

import PatternUnify.ConstraintInfo as UC

import Control.Monad (forM)
import Data.Foldable (foldlM)


import Debug.Trace (trace)

--import qualified Solver

mapSnd f (a,b) = (a, f b)
mapFst f (a,b) = (f a, b)


--errorMsg :: [(Region, String)] -> String
--errorMsg pairs =
--  List.intercalate "\n" $
--  map (\(reg, err) -> show reg ++ ": " ++ err ) pairs

checker :: SolverConfig -> TypeChecker
checker config (valNameEnv, typeContext) term =
  let
    toPos (reg, err) = case reg of
      Tm.BuiltinRegion -> (Nothing, err)
      pos@(Tm.SourceRegion _ _ _) -> (Just pos, err)
    (typeGlobals, typeLocals) = splitContext typeContext
    (valGlobals, valLocals) = splitContext  valNameEnv
    genResult =  getConstraints (WholeEnv valLocals typeLocals valGlobals typeGlobals) term
    soln = solveConstraintM config genResult
    -- solvedString = case solvedMetas of
    --   Left _ -> ""
    --   Right pairs ->
    --     "Solved metas:\n"
    --     ++ (intercalate "\n" (map (\(s, v) -> s ++ " := " ++ Tm.prettyString v) pairs))
  in
    case soln of
      Left pairs -> Left $ map toPos pairs
      Right (tp, nf, subs, metaLocs) -> Right $
        let
          subbedVal = LN.runFreshM $ Tm.eval subs nf
          pairToMaybe (nm, val) = do
            loc <- Map.lookup nm metaLocs
            return (loc, val)
          namePairs = Maybe.catMaybes $ map pairToMaybe $ Map.toList subs
        in
          (tp, subbedVal, namePairs)


conStar = Tm.SET

getConstraints :: WholeEnv -> ITerm_ -> ConstraintM (Tm.Nom, Tm.VAL)
--getConstraints env term | trace ("\n\n**************************************\nChecking, converted " ++ show (iPrint_ 0 0 term))  $ trace ("\n  into " ++ Tm.prettyString (constrEval (map (mapFst Global) $ globalTypes env, map (mapFst Global) $ globalValues env) term ) ++ "\n\n") False
--  = error "genConstraints"
getConstraints env term =
  do
    finalType <- iType0_ env term
    finalVar <- freshTopLevel Tm.SET
    finalValue <- evaluate 0 (L startRegion $ Inf_ term) env
    unifySets UC.TypeOfProgram (showIt term) startRegion finalType (Tm.meta finalVar) env
    return (finalVar, finalValue)

iType0_ :: WholeEnv -> ITerm_ -> ConstraintM ConType
iType0_ = iType_ 0

iType_ :: Int -> WholeEnv -> ITerm_ -> ConstraintM ConType
iType_ iiGlobal g lit@(L reg it) = --trace ("ITYPE " ++ show (iPrint_ 0 0 lit)) $
  do
    result <- iType_' iiGlobal g it
    return $ --trace ("===>  RET ITYPE " ++ show (iPrint_ 0 0 lit) ++ " :: " ++ Tm.prettyString result) $
      result
  where
    iType_' ii g m@(Meta_ s) = do
      metaType <- freshType reg g
      ourNom <- return $ LN.s2n s --freshNom s
      recordSourceMeta reg ourNom
      --Add metavariable to our context, and return its type
      _ <- declareWithNom reg g metaType ourNom
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
    --Similar to Pi
    iType_' ii g (Sigma_ tyt tyt')
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
    iType_' ii g e@(_ :$: _)
      =     trace ("CHECKING APP " ++ showIt lit) $ do
                let
                  unravelApp (L _ (f :$: g)) accum = unravelApp f (g : accum)
                  unravelApp f accum = (f, accum)

                  (topFn, args) = unravelApp lit []

                  mkVars argExp = trace ("UNRAVELED APP INTO " ++ showIt topFn ++ "  and  " ++ show (map showCt args) ) $ do
                      piArg <- freshType (region argExp) g
                      return (piArg)

                topFnTypeVar@(Tm.N (Tm.Meta fnNom) _) <- freshType (region topFn) g
                vars <- mapM  mkVars args
                argVals <- mapM (\x -> evaluate ii x g) args
                let varNoms = map (\ (Tm.N (Tm.Meta alpha) _) -> alpha ) vars


                topFnTypeVal <- trace ("APP CALLING ITYPE " ++ showIt topFn) $ iType_ ii g topFn
                unifySets (AppFnType reg (showIt topFn) fnNom) (showIt topFn) (region topFn) topFnTypeVar topFnTypeVal g
                retTypeVar@(Tm.N (Tm.Meta retNom) _) <- freshType (region lit) g
                let
                  freeVars = List.nub $ concatMap (Tm.fvs . snd) $ reverse $ valueEnv g
                  progContextFor argNum = Application reg argNum (zip argVals varNoms) retNom freeVars

                  doUnif (fnType, argNum) (argExp, piArg) = do
                    piBodyFn <- fresh (region argExp) g (piArg Tm.--> Tm.SET)
                    unifySets (progContextFor argNum) (showIt lit)  reg (fnType) (Tm.PI piArg piBodyFn) g
                    --Ensure that the argument has the proper type
                    trace ("APP CALLING CTYPE " ++ showCt argExp) $ cType_ ii g argExp piArg
                    --Get a type for the evaluation of the argument
                    argVal <- evaluate ii argExp g
                    --Our resulting type is the application of our arg type into the
                    --body of the pi type
                    retType <- piBodyFn Tm.$$ argVal
                    --trace ("APP " ++ show (iPrint_ 0 0 lit) ++ "\n  return " ++ Tm.prettyString retType) $
                    return (retType, argNum + 1)

                --Make a nice variable referring to our return type, easy to find in graph
                (retType, _) <- foldlM doUnif (topFnTypeVar, 1) $ zip args vars
                unifySets (AppRetType reg retNom) ("result of application " ++ showIt lit) reg retType retTypeVar g
                return retTypeVar


    iType_' ii g Nat_                  =  return conStar
    iType_' ii g (NatElim_ m mz ms n)  =
      do  cType_ ii g m (Tm.Nat Tm.--> Tm.SET)
          --evaluate ii $ our param m
          mVal <- evaluate ii m g
          --Check that mz has type (m 0)
          ourApp1 <- (mVal Tm.$$ Tm.Zero)
          cType_ ii g mz ourApp1
          --Check that ms has type ( (k: N) -> m k -> m (S k) )
          ln <- freshNom $ "l"
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
          mVal <- evaluate ii m g
          nVal <- evaluate ii n g

          mType <- Tm.vmVType aVal
          cType_ ii g m mType

          mnType <- Tm.mnVType aVal mVal
          cType_ ii g mn mnType

          mcType <- Tm.mcVType aVal mVal
          cType_ ii g mc mcType

          cType_ ii g n $ Tm.Nat

          cType_ ii g vs ((Tm.Vec aVal nVal ))
          vsVal <- evaluate ii vs g

          Tm.vResultVType mVal nVal vsVal


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
          let
            eqC =
              ((Tm.Eq yVal xVal aVal))
          cType_ ii g eq eqC
          eqVal <- evaluate ii eq g
          (mVal Tm.$$$ [xVal, yVal])

    iType_' ii g (Fst_ pr) = do
      pairType <- iType_ ii g pr
      sType <- freshType (region pr) g
      tType <- fresh (region pr) g (sType Tm.--> conStar)
      unifySets ElimEdge (showIt lit) reg pairType (Tm.SIG sType tType) g
      --Head has the type of the first elem
      return sType

    iType_' ii g (Snd_ pr) = do
      pairType <- iType_ ii g pr
      sType <- freshType (region pr) g
      tType <- fresh (region pr) g (sType Tm.--> conStar)
      unifySets ElimEdge (showIt lit) reg pairType (Tm.SIG sType tType) g
      prVal <- evaluate ii (L reg $ Inf_ pr) g
      headVal <- prVal Tm.%% Tm.Hd
      --Head has second type, with first val given as argument
      tType Tm.$$ headVal


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
              --Avoid problems that don't affect unification
              let areSame = ( (null $ Tm.fmvs tyAnnot ++ Tm.fmvs tyInferred) && tyAnnot == tyInferred)
              case areSame of
                --Get rid of a bunch of useless constraints
                True -> return ()
                _ ->
                  unifySets SignatureCheck (showCt lct) reg tyInferred tyAnnot g

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
        argVal <- return $ Tm.var argName --evalInEnv g $ Tm.var argName --iToUnifForm ii newEnv arg
        unifySets FnType (showCt lct) reg fnTy (Tm.PI argTy returnTyFn)  g
        returnTy <- freshType (region body) newEnv
        appedTy <- (returnTyFn Tm.$$ argVal)
        unifySets FnBody (showCt lct) reg returnTy appedTy newEnv
        --unify  returnTyFn (Tm.lam argName returnTy) (argTy Tm.--> conStar) g --TODO is argVal good?
        --Convert bound instances of our variable into free ones
        let subbedBody = cSubst_ 0 arg body
        cType_  (ii + 1) newEnv subbedBody returnTy

    cType_' ii g (Pair_ x y) sigTy = do
      sType <- freshType (region x) g
      tType <- fresh (region y) g (sType Tm.--> conStar)
      unifySets Ctor (showCt lct) reg sigTy (Tm.SIG sType tType) g
      --Head has the type of the first elem
      cType_ ii g x sType
      --Tail type depends on given argument
      fstVal <- evaluate ii x g
      appedTy <- (tType Tm.$$ fstVal)
      cType_ ii g y appedTy

    cType_' ii g Zero_      ty  =  unifySets Ctor (showCt lct) reg ty Tm.Nat g
    cType_' ii g (Succ_ k)  ty  = do
      unifySets Ctor (showCt lct) reg ty Tm.Nat g
      cType_ ii g k Tm.Nat

    cType_' ii g (FZero_ n)      ty  =  do
      cType_ ii g n Tm.Nat
      nVal <- evaluate ii n g
      --Never can make an element of Fin 0
      unifySets Ctor (showCt lct) reg ty (Tm.Fin (Tm.Succ nVal) ) g
    cType_' ii g (FSucc_ n f)  ty  = do
      cType_ ii g n Tm.Nat
      nVal <- evaluate ii n g
      --Decrease our index each time we check
      cType_ ii g f (Tm.Fin nVal)
      unifySets Ctor (showCt lct) reg ty (Tm.Fin (Tm.Succ nVal)) g


    cType_' ii g (Nil_ a) ty =
      do
          bVal <- freshType reg g
          unifySets Ctor (showCt lct) reg ty (mkVec bVal Tm.Zero) g
          cType_ ii g a conStar
          aVal <- evaluate ii a g
          unifySets Ctor (showCt lct) reg aVal bVal g
    cType_' ii g (Cons_ a n x xs) ty  =
      do  --bVal <- freshType (region a) g
          aVal <- evaluate ii a g
          nVal <- evaluate ii n g
          --k <- fresh (region n) g Tm.Nat
          --Trickery to get a Type_ to a ConType
          --let kSucc = Tm.Succ k
          unifySets Ctor (showCt lct) reg ty (mkVec aVal (Tm.Succ nVal)) g
          cType_ ii g a conStar


          --unifySets reg aVal bVal g

          cType_ ii g n Tm.Nat

          --Make sure our numbers match

          --unify reg nVal kSucc Tm.Nat g

          --Make sure our new head has the right list type
          cType_ ii g x aVal
          --Make sure our tail has the right length
          cType_ ii g xs (mkVec aVal nVal)

    cType_' ii g (Refl_ a z) ty =
      do  aVal <- evaluate ii a g
          --bVal <- freshType (region a) g
          xVal <- fresh (region z) g aVal
          yVal <- fresh (region z) g aVal
          unifySets Ctor (showCt lct) reg ty (mkEq aVal xVal yVal) g
          --Check that our type argument has kind *
          cType_ ii g a conStar
          --Get evaluation constraint for our type argument


          --Check that our given type is the same as our inferred type --TODO is this right?
          --unifySets reg aVal bVal g

          --Check that the value we're proving on has type A
          cType_ ii g z aVal

          --evaluate ii $ the value that we're proving equality on
          zVal <- evaluate ii z g

          --Show constraint that the type parameters must match that type
          unify Ctor (showCt lct) reg zVal xVal aVal g
          unify Ctor (showCt lct) reg zVal yVal aVal g
