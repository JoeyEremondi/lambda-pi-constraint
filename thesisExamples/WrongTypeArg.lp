let myFun = (\ _ x y -> 0) :: forall (A :: *). A -> A -> Nat

let myApp = (myFun _ 0 *) :: Nat
