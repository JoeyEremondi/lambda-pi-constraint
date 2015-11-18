module Constraint where

import qualified Common

--We index type variables as unique integers
newtype TypeVar = TypeVar {varIdent :: Int}

--Type we can unify over: either a type literal
--Or a type variable
data CType =
  VarType TypeVar
  | LitType Common.Type_

data Constraint =
  ConstrEquals CType CType

(===) :: CType -> CType -> Constraint
t1 === t2 = ConstrEquals t1 t2
