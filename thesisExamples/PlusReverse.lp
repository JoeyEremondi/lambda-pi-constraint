-- addition of natural numbers
let plus = (\ y x ->
  (natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ
  ) x y ) :: Nat -> Nat -> Nat

let p0PlusNisN =
  (\ x ->
    Refl Nat x
  )
  :: (forall (n :: Nat) . Eq Nat (plus 0 n) n)
