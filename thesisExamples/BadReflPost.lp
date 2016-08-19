-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

assume pNPlus0isN
  :: forall n :: Nat . Eq Nat (plus n 0) n

let succPlus =
  (\n -> pNPlus0isN (Succ n))
  :: forall n :: Nat . Eq Nat  (Succ n) (plus (Succ n) 0)
