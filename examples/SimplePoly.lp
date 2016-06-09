let myFun = (\ a x y -> x) :: forall (a :: *) . a -> a -> a

let natNil = Nil Nat

let myApp = myFun _ natNil 0
