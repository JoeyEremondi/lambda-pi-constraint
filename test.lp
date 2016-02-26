-- addition of natural numbers
--let id    = (\ x y -> y) :: forall (x :: *) .  x -> x

--let intId = (\x -> x) :: Nat -> Nat

--let x = (id _ 0) :: Nat

--let app = (\t1 f x -> f x) :: forall (t1 :: *) . (t1 -> Nat) ->  t1 -> Nat

let x = natElim
