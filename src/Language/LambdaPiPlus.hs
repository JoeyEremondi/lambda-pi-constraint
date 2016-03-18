{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.LambdaPiPlus
  ( CompileContext
  , compile
  , initialContext
  , noPreludeContext
  ) where

import qualified Language.LambdaPiPlus.Internals as Internal

import Language.Haskell.TH.Syntax (qRunIO)

import Common (lpte, lpve)

import Language.Haskell.TH.Lift

import PatternUnify.Tm as Tm

type CompileContext = Internal.CompileContext

noPreludeContext = Internal.emptyContext

compile = Internal.compile

initialContext :: CompileContext
initialContext = $(
  do
    preludeText <- qRunIO $ readFile "prelude.lp"
    let
      preludeContext =
        case Internal.compile preludeText Internal.emptyContext of
          Left e -> error $ "ERROR compiling prelude: " ++ show e
          Right ctx -> ctx
    [|preludeContext|]
  )
