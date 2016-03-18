module LambdaPiPlus
  ( CompileContext
  , compile
  ) where

type CompileContext = Int

prelude :: CompileContext
prelude = error "TODO prelude"

compile :: String -> CompileContext -> Either String CompileContext
compile source context = error "TODO implement"
