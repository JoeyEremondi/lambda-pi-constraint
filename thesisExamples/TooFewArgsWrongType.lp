let myFun = (\ x y -> y) ::  Vec Nat 0 -> Nat -> Nat

let myApp = (myFun 0) :: Nat
