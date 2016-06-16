{-#  OPTIONS --type-in-type #-}
module Bias

import IdrisPrelude

myFun : (a : Type) -> a -> a -> a -> Nat
myFun a x y z = Zero

myApp1 : Nat
myApp1 = myFun _ Zero Zero (IdrisPrelude.Nil Nat)

myApp2 : Nat
myApp2 = myFun _ (Nil Nat) Zero Zero
