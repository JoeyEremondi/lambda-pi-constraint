let myFun = (\ _ x y -> y) :: forall (a :: *) . a -> Nat -> Nat

let myApp = (myFun _ 0 (Nil Nat))
