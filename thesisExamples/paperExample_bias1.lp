
assume pairZipWith :: forall (a :: *) (b :: *) (n :: Nat) . ( (a , a) -> b) -> list a -> list a -> list b

let plus = (\ y x ->
  (natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ
  ) x y ) :: Nat -> Nat -> Nat

let bool = Fin 2

assume myList :: list bool

let myVal = foldr _ _ plus 0 myList :: Nat
