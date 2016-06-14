{-#  OPTIONS --type-in-type #-}
module TooFewArgs where

open import AgdaPrelude

myFun : (a : Set) -> a -> a -> a
myFun a x y = x

id : (a : Set) -> a -> a
id a x = x

myApp : Nat
myApp = (id _ myFun) _ Zero
