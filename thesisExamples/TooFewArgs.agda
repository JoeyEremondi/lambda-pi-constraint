{-#  OPTIONS --type-in-type #-}
module TooFewArgs where

open import AgdaPrelude

myFun : (a : Set) -> a -> a -> a
myFun a x y = x

myApp : Nat
myApp = myFun _ Zero
