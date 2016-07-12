{-#  OPTIONS --type-in-type #-}
module TooManyArgs

import IdrisPrelude

myFun : (a : Type) -> a -> a -> a
myFun a x y = x

myApp : Nat
myApp = myFun _ Zero Zero Zero Zero
