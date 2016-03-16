let Prod =
  (\s t -> exists (x :: s) . t )
  :: * -> * -> *

let zeroes = ( 0 , 0 ) :: Prod Nat Nat
