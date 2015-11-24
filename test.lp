-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat -> Nat)           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ
