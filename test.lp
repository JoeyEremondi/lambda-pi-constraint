-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

-- append two vectors

let append =
  ( \ a -> vecElim a
             (\ m _ -> forall (n :: Nat) . Vec a n -> Vec a (plus m n))
             (\ _ v -> v)
             (\ m v vs rec n w -> Cons a (plus m n) v (rec n w)))
  ::  forall (a :: *) (m :: Nat) (v :: Vec a m) (n :: Nat) (w :: Vec a n).
      Vec a (plus m n)
