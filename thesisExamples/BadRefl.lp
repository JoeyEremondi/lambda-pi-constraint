-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ


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


-- the other direction requires induction on N:
let succPlus =
  (\n -> pNPlus0isN (Succ n))
  :: forall n :: Nat . Eq Nat  (Succ n) (plus (Succ n) 0)
