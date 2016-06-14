{-#  OPTIONS --type-in-type #-}
module ArgsWrongOrder where

open import AgdaPrelude

myFun : (a : Set) -> a -> Nat -> Nat
myFun _ x y = y

myApp = myFun _ Zero (Nil Nat)
