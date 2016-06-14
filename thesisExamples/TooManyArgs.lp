let myFun = (\ a x y -> x) :: forall (a :: *) . a -> a -> a

let myApp = myFun _ 0 1 2
