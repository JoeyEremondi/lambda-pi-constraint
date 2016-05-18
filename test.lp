--let x = 3 :: Nat

--let id = (\_ x -> x) :: forall (a :: *) . a -> a

let natIf =
  (\_ x y n ->  natElim _ x (\ _ _ -> y) n ) :: forall (a :: *) . a -> a -> Nat -> a

let test = natIf _ 3 (3 , 3) 0

--let test = natIf _ (3 , 3) 3 0
