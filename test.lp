-- addition of natural numbers
--let id    = (\ x y -> y) :: forall (x :: *) .  x -> x

--let intId = (\x -> x) :: Nat -> Nat

--let x = (id _ 0) :: Nat

--let app = (\t1 f x -> f x) :: forall (t1 :: *) . (t1 -> Nat) ->  t1 -> Nat


-- an eliminator for natural numbers that has special
-- cases for 0 and 1
let nat1Elim =
  ( \ m m0 m1 ms -> natElim m m0
                            (\ p rec -> natElim (\ n -> m (Succ n)) m1 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 ->
     (forall n :: Nat . m (Succ n) -> m (Succ (Succ n))) ->
     forall (n :: Nat) . m n

-- an eliminator for natural numbers that has special
-- cases for 0, 1 and 2
let nat2Elim =
  ( \ m m0 m1 m2 ms -> nat1Elim m m0 m1
                                (\ p rec -> natElim (\ n -> m (Succ (Succ n))) m2 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 -> m 2 ->
     (forall n :: Nat . m (Succ (Succ n)) -> m (Succ (Succ (Succ n)))) ->
     forall (n :: Nat) . m n
