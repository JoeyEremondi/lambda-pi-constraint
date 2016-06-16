{-#  OPTIONS --type-in-type #-}
module Bias where

open import AgdaPrelude

myFun : (a : Set) -> a -> a -> a -> a
myFun a x y z = x

--myApp1 = myFun _ Zero Zero (Nil Nat)

myApp2 = myFun _ (Nil Nat) Zero Zero
