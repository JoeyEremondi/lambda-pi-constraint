-- addition of natural numbers
--let id    = (\ x y -> y) :: forall (x :: *) .  x -> x

--let intId = (\x -> x) :: Nat -> Nat

--let x = (id _ 0) :: Nat

--let app = (\t1 f x -> f x) :: forall (t1 :: *) . (t1 -> Nat) ->  t1 -> Nat

-- an eliminator for natural numbers that has special
-- cases for 0 and 1
let nat1Elim =
  ( \ m m0 m1 ms -> natElim m m0
                            (\ p rec -> natElim (\ k -> m (Succ k)) m1 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 ->
     (forall l :: Nat . m (Succ l) -> m (Succ (Succ l))) ->
     forall (n :: Nat) . m n
