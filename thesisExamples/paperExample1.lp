
assume foldr :: forall (a :: *) (b :: *) (n :: Nat) . (a -> b -> b) -> b -> Vec a n -> b

let plus = (\ y x ->
  (natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ
  ) x y ) :: Nat -> Nat -> Nat

let bool = Fin 2

assume myList :: Vec bool 1

let myVal = foldr _ _ _ plus 0 myList :: bool
