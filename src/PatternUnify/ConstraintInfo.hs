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

import Common (Region)
import Text.Parsec (SourcePos)


newtype ProbId = ProbId {probIdToName :: Nom}
  deriving (Eq, Show, Pretty, Generic)

data ConstraintInfo = ConstraintInfo
  { edgeType    :: ConstraintType
  , edgeEqnInfo :: EqnInfo
  } deriving (Eq, Show, Generic)

data ConstraintType =
  InitConstr ProbId
  | DefnUpdate Nom
  | ProbUpdate ProbId
  | DefineMeta Nom
  | DerivedEqn ProbId
  deriving (Eq, Show, Generic)

data EqnInfo =
  EqnInfo
  { creationInfo :: CreationInfo
  , infoRegion   :: Region
  , isCF         :: IsCF
  } deriving (Eq, Show, Generic)

data CreationInfo = Initial | CreatedBy ProbId
  deriving (Eq, Show, Generic)

data IsCF = Factual | CounterFactual
  deriving (Eq, Ord, Show, Generic)
