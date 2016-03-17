-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ


-- symmetry of (general) equality
let symm =
  ( \ a -> eqElim a
             (\ x y eq_x_y -> Eq a y x)
             (\ x -> Refl a x) )
  :: forall (a :: *) (x :: a) (y :: a) .
     Eq a x y -> Eq a y x

-- Leibniz prinicple (look at the type signature)
let leibniz =
  ( \ a b f -> eqElim a
                 (\ x y eq_x_y -> Eq b (f x) (f y))
                 (\ x -> Refl b (f x)) )
  :: forall (a :: *) (b :: *) (f :: a -> b) (x :: a) (y :: a) .
     Eq a x y -> Eq b (f x) (f y)


-- the other direction requires induction on N:
let pNPlus0isN =
  natElim ( \ n -> Eq Nat (plus n 0) n )
          ( Refl Nat 0 )
          ( \ n' rec -> leibniz Nat Nat Succ (plus n' 0) n' rec )
  :: forall n :: Nat . Eq Nat (plus n 0) n

let geq = (\ x y -> exists (z :: Nat) . Eq Nat x (plus y z) ) :: Nat -> Nat -> *

let gt =
  (\ x y -> geq x (Succ y))
  :: Nat -> Nat -> *

--let natsAreInf =
--  (\n -> (Succ n, (0, Refl _ _) ) )
--  :: forall (n :: Nat) . exists (m :: Nat) . geq m (Succ n)


--let natsAreInf =
--  (\n -> (Succ n, (0, Refl _ _) ) )
--  :: forall (n :: Nat) . exists (m :: Nat) . gt m n

--This version should work?
let natsAreInf =
  (\n -> (Succ n, (0, symm _ _ _ (pNPlus0isN (Succ n))) ) )
  :: forall (n :: Nat) . exists (m :: Nat) . gt m n
