
assume myFun :: forall (a :: *) . a -> a -> a -> a

let myApp1 = myFun _ Zero Zero (Nil Nat)

--let myApp2 = myFun _ (Nil Nat) Zero Zero
