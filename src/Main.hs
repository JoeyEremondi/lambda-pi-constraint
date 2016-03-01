module Main where

--import qualified Original as O
import qualified ConstraintBased as CB
import Common

import PatternUnify.Test

main :: IO ()
main = repLP (CB.checker (unifve, unifte) ) True
