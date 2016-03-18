module Language.LambdaPiPlus
  ( CompileContext
  , compile
  ) where

import Text.Parsec.Pos (SourcePos)

type CompileContext = Int

prelude :: CompileContext
prelude = error "TODO prelude"

compile :: String -> CompileContext -> Either (Maybe SourcePos, String) CompileContext
compile source context = error "TODO implement"
