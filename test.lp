let vident =
  (\ a n x ->
    vecElim a
    (\_ _ -> Nat)
    (0)
    (\n h t rest _ -> 1))
  :: forall (a :: *) (m :: Nat) (v :: Vec a m) . Nat

-- append two vectors
{-
let append =
  ( \ a -> vecElim a
             (\ m _ -> forall (n :: Nat) . Vec a n -> Vec a (plus m n))
             (\ _ v -> v)
             (\ m v vs rec n w -> Cons a (plus m n) v (rec n w)))
  ::  forall (a :: *) (m :: Nat) (v :: Vec a m) (n :: Nat) (w :: Vec a n).
      Vec a (plus m n)
-}
