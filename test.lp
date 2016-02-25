-- addition of natural numbers
--let id    = (\ a x -> x) :: forall (a :: *) . a ->  a -> a

--let intId = (\x -> x) :: Nat -> Nat

--let x = id _ intId :: Nat

let app = (\t1 f x -> f x) :: forall (t1 :: *) . (t1 -> Nat) ->  t1 -> Nat
