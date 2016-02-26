-- addition of natural numbers
--let id    = (\ x y -> y) :: forall (x :: *) .  x -> x

--let intId = (\x -> x) :: Nat -> Nat

--let x = (id _ 0) :: Nat

--let app = (\t1 f x -> f x) :: forall (t1 :: *) . (t1 -> Nat) ->  t1 -> Nat

-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ
