--let x = 3 :: Nat

let id = (\_ x -> x) :: forall (a :: *) . a -> a

--let natIf3 =
--  (\_ x y z n ->  nat1Elim _ x y (\ _ _ -> z) n ) :: forall (a :: *) . a -> a -> a -> Nat -> a

--let myFun = (\x -> x) :: Nat -> Nat

--let myPair = (3,3) :: exists (x :: Nat) . Nat

--let test = natIf3 _ myPair myPair myPair 0

--let test1 = natIf3 _ 1 (Nil Nat) 3 0

--let test2 = natIf3 _ (Nil Nat) 2 3 0
