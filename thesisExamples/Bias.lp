
let myFun = (\ a x y z -> x) :: forall (a :: *) . a -> a -> -> a

let myApp1 = myFun _ Zero Zero (Nil Nat)

--let myApp2 = myFun _ (Nil Nat) zero Zero
