--let x = 3 :: Nat

--let id = (\_ x -> x) :: forall (a :: *) . a -> a

let nat1Elim =
  ( \ m m0 m1 ms -> natElim m m0
                            (\ p rec -> natElim (\ n -> m (Succ n)) m1 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 ->
     (forall n :: Nat . m (Succ n) -> m (Succ (Succ n))) ->
     forall (n :: Nat) . m n

let natIf3 =
  (\_ x y z n ->  nat1Elim _ x y (\ _ _ -> z) n ) :: forall (a :: *) . a -> a -> a -> Nat -> a

--let myFun = (\x -> x) :: Nat -> Nat

--let myPair = (3,3) :: exists (x :: Nat) . Nat

--let test = natIf3 _ 1 ((\x -> x) :: Nat -> Nat) 3 0

--let test1 = natIf3 _ 1 (Nil Nat) 3 0

--let natNil = Nil Nat

let test2 = natIf3 _ (Nil *) 2 3 0
