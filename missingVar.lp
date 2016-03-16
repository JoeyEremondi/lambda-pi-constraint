let Prod =
  (\s t -> exists (x :: s) . t )
  :: * -> * -> *

-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

let zeroes = ( 0 , 0 ) :: Prod Nat Nat

let v1 = (fst zeroes) :: Nat

let v2 = (snd zeroes) :: Nat

let geq = (\ x y -> exists (z :: Nat) . Eq Nat x (plus y z) ) :: Nat -> Nat -> *

let ident0 =
  (\ x -> Refl Nat (plus 0 x))
  :: forall (x :: Nat) . Eq Nat x (plus 0 x)

let geq0 =
  (\n -> (n , ident0 n) )
  :: forall (n :: Nat ) . geq n 0

let natsAreInf =
  (\n -> (Succ n, _) )
  :: forall (n :: Nat) . exists (m :: Nat) . geq m (Succ n)
