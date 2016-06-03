let symm =
  ( \ a -> eqElim a
             (\ x y eq_x_y -> Eq a y x)
             (\ x -> Refl a x) )
  :: forall (a :: *) (x :: a) (y :: a) .
     Eq a x y -> Eq a y x

let bias = (\ x y -> symm * _ _ (Refl * x) ) :: forall (x :: *) (y :: *) . Eq * x x
