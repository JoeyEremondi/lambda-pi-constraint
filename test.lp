let gt =
  (\ x y -> geq x (Succ y))
  :: Nat -> Nat -> *

let leq = (\ x y -> geq y x) :: Nat -> Nat -> *

let lt = (\ x y -> gt y x) :: Nat -> Nat -> *

let geq0 =
  (\n -> (n , p0PlusNisN n) )
  :: forall (n :: Nat ) . geq n 0

let natsAreInf =
  (\n -> (Succ n, (0, symm Nat (plus (Succ n) 0) (Succ n) (pNPlus0isN (Succ n))) ) )
  :: forall (n :: Nat) . exists (m :: Nat) . gt m n
