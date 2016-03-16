------ We can build binary sums out of Bools and Products
let sum =
  (\ s t -> exists (b :: Bool) . boolElim (\_ -> *) s t )
  :: * -> * -> *
