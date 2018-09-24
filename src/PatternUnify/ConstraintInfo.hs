{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

module PatternUnify.ConstraintInfo where



import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import qualified Control.Monad.Writer as Writer

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import Debug.Trace (trace)
import GHC.Generics

import Unbound.Generics.LocallyNameless hiding (join, restrict)
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
--import Unbound.LocallyNameless.Types (GenBind(..))

import PatternUnify.Kit
import PatternUnify.Tm

--import Debug.Trace (trace)

import Data.List (union)

import qualified Top.Interface.Basic as Basic

import qualified Top.Implementation.TypeGraph.ClassMonadic as CM

import qualified Top.Implementation.TypeGraph.ApplyHeuristics as Heur

import Top.Solver (LogEntries)

import PatternUnify.Tm (Region (..))
import Text.Parsec (SourcePos)


newtype ProbId = ProbId {probIdToName :: Nom}
  deriving (Eq, Show, Pretty, Generic, Ord)

data ConstraintInfo = ConstraintInfo
  { edgeType     :: ConstraintType
  , edgeEqnInfo  :: EqnInfo
  , edgeEqn      :: (VAL, VAL)
  , typeOfValues :: Type
  , maybeHint    :: Maybe String
  } deriving (Eq, Show, Generic)

data ProgramContext =
--  AppFnType Region String VAL
  AppRetType Region VAL
  --App region, argNum, fn type, arg value-type pairs, return type, free vars
  | Application Region Int String VAL [(VAL, VAL)] VAL [Nom]
  | TypeOfProgram
  | VarDecl
  | ElimEdge
  | SignatureCheck
  | FnType
  | FnBody
  | Ctor
  deriving (Eq, Show, Generic)

applicationEdgeRegion :: ProgramContext -> Maybe Region
--applicationEdgeRegion (AppFnType reg _ _) = Just reg
applicationEdgeRegion (Application reg _ _ _ _ _ _) = Just reg
applicationEdgeRegion (AppRetType reg _) = Just reg
applicationEdgeRegion _ = Nothing

isRightEdge :: ConstraintType -> Bool
isRightEdge (ChoiceEdge RightChoice _ _) = True
isRightEdge _ = False


instance Alpha ProgramContext

instance Alpha EqnInfo


instance Alpha ProbId
instance Subst VAL ProbId

instance Alpha IsCF

instance Subst VAL IsCF

instance Subst VAL ProgramContext where
  subst _ _ a = a
  substs _ a = a
instance Subst VAL Region where
  subst _ _ a = a
  substs _ a = a
instance Subst VAL EqnInfo where
  subst _ _ a = a
  substs _ a = a


instance Alpha CreationInfo
--NEVER traverse into cosntraint info for substitution
instance Subst VAL ConstraintInfo where
  subst _ _ a = a
  substs _ a = a

data ChoiceEdge = LeftChoice | RightChoice
  deriving (Eq, Ord, Show, Generic)

data ConstraintType =
  InitConstr ProbId
  | MetaUpdate (Nom, VAL)
  -- | DefnUpdate Nom
  -- | ProbUpdate ProbId
  | DefineMeta Nom
  | DerivedEqn ProbId
  | ChoiceEdge ChoiceEdge Nom (VAL, VAL)
  deriving (Eq, Show, Generic)

data EqnInfo =
  EqnInfo
  { creationInfo     :: CreationInfo
  , infoRegion       :: Region
  , isCF             :: IsCF
  , programContext   :: ProgramContext
  , typeOfString     :: String
  , initialCreatorId :: Maybe ProbId
  , isImpliedEquality :: Bool
  , extraDeps :: [ProbId]
  } deriving (Eq, Show, Generic)


constraintPid :: ConstraintInfo -> Maybe ProbId
constraintPid info = case edgeType info of
  InitConstr pid -> Just pid
  DerivedEqn pid -> Just pid
  _ -> Nothing


data CreationInfo = Initial | CreatedBy ProbId
  deriving (Eq, Show, Generic)

data IsCF = Factual | CounterFactual
  deriving (Eq, Ord, Show, Generic)



-- choiceInfo reg choice n x y =
--   ConstraintInfo
--     (ChoiceEdge choice n)
--     (EqnInfo Initial reg Factual)
--     (x,y)
