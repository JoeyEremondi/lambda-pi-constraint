{-#  OPTIONS --type-in-type #-}
module TooManyArgs where

open import AgdaPrelude

myFun : (a : Set) -> a -> a -> a
myFun a x y = x

id : (a : Set) -> a -> a
id a x = x

myApp = (id _ myFun) _ Zero (Succ Zero) (Succ (Succ Zero)) Zero
