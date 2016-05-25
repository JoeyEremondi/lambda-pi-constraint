--let x = 3 :: Nat

--let id = (\_ x -> x) :: forall (a :: *) . a -> a

-- an eliminator for natural numbers that has special
-- cases for 0 and 1
let nat1Elim =
  ( \ m m0 m1 ms -> natElim m m0
                            (\ p rec -> natElim (\ n -> m (Succ n)) m1 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 ->
     (forall n :: Nat . m (Succ n) -> m (Succ (Succ n))) ->
     forall (n :: Nat) . m n

let natIf3 =
  (\_ x y z n ->  nat1Elim _ x y (\ _ _ -> z) n ) :: forall (a :: *) . a -> a -> a -> Nat -> a

let test = natIf3 _ (1,1) (2 , 2) (3,3) 0

--let test1 = natIf3 _ 1 (2 , 2) 3 0

--let test2 = natIf3 _ (1 , 1) 2 3 0
