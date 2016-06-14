{-#  OPTIONS --type-in-type #-}
module TooFewArgsWrongType where

open import AgdaPrelude

myFun : Vec Nat Zero -> Nat -> Nat
myFun x y = y

myApp : Nat
myApp = (myFun Zero)
