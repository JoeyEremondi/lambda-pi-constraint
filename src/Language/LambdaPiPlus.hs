module LambdaPiPlus
  ( CompileContext
  , compile
  ) where

type CompileContext = Int

compile :: String -> CompileContext -> Either String CompileContext
compile source context = error "TODO implement"
