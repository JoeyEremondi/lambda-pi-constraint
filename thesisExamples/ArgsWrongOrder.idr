module ArgsWrongOrder

import IdrisPrelude

%hide Prelude.Nat.Nat


myFun : (a : Type) -> a -> Nat -> Nat
myFun _ x y = y

myApp : Nat
myApp = myFun _ Zero (IdrisPrelude.Nil Nat)
