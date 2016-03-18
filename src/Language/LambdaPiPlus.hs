{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.LambdaPiPlus
  ( CompileContext
  , ParseResult
  , parse
  , compile
  , initialContext
  , noPreludeContext
  ) where

import qualified Language.LambdaPiPlus.Internals as Internal

import Language.Haskell.TH.Syntax (qRunIO)

import Common (lpte, lpve)

import Language.Haskell.TH.Lift

import PatternUnify.Tm as Tm

import Text.Parsec.Pos (SourcePos)

type CompileContext = Internal.CompileContext
type ParseResult = Internal.ParseResult
type Output = String

noPreludeContext = Internal.emptyContext

parse :: String -> Either [(Maybe SourcePos, String)] ParseResult
parse = Internal.parse

compile :: ParseResult -> CompileContext -> Either [(Maybe SourcePos, String)] (CompileContext, Output)
compile = Internal.compile

initialContext :: CompileContext
initialContext = $(
  do
    preludeText <- qRunIO $ readFile "prelude.lp"
    let
      preludeContext =
        let
          compResult =
            do
              parseResult <- Internal.parse preludeText
              fst <$> Internal.compile parseResult Internal.emptyContext
        in
          case compResult of
            Left e -> error $ "ERROR compiling prelude: " ++ show e
            Right ctx -> ctx
    [|preludeContext|]
  )
