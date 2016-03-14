let nat1Elim =
  ( \ m m0 m1 ms -> natElim m m0
                            (\ p rec -> natElim (\ n -> m (Succ n)) m1 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 ->
     (forall n :: Nat . m (Succ n) -> m (Succ (Succ n))) ->
     forall (n :: Nat) . m n



-- unit type
let Unit = Fin 1
-- constructor
let U = FZero 0

-- an eliminator for natural numbers that has special
-- cases for 0 and 1



-- an eliminator for natural numbers that has special
-- cases for 0, 1 and 2
let nat2Elim =
  ( \ m m0 m1 m2 ms -> nat1Elim m m0 m1
                                (\ p rec -> natElim (\ n -> m (Succ (Succ n))) m2 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 -> m 2 ->
     (forall n :: Nat . m (Succ (Succ n)) -> m (Succ (Succ (Succ n)))) ->
     forall (n :: Nat) . m n


-- type of booleans
let Bool = Fin 2

-- constructors
let False = FZero 1
let True  = FSucc 1 (FZero 0)





let boolElim =
( \ m mf mt -> finElim ( nat2Elim (\ n -> Fin n -> *)
                                 (\ _ -> Unit) (\ _ -> Unit)
                                 (\ x -> m x)
                                 (\ _ _ _ -> Unit) )
                      ( nat1Elim ( \ n -> nat1Elim (\ n -> Fin (Succ n) -> *)
                                                   (\ _ -> Unit)
                                                   (\ x -> m x)
                                                   (\ _ _ _ -> Unit)
                                                   n (FZero n))
                                 U mf (\ _ _ -> U) )
                      ( \ n f _ -> finElim ( \ n f -> nat1Elim (\ n -> Fin (Succ n) -> *)
                                                               (\ _ -> Unit)
                                                               (\ x -> m x)
                                                               (\ _ _ _ -> Unit)
                                                               n (FSucc n f) )
                                           ( natElim
                                               ( \ n -> natElim
                                                          (\ n -> Fin (Succ (Succ n)) -> *)
                                                          (\ x -> m x)
                                                          (\ _ _ _ -> Unit)
                                                          n (FSucc (Succ n) (FZero n)) )
                                               mt (\ _ _ -> U) )
                                           ( \ n f _ -> finElim
                                                          (\ n f -> natElim
                                                                      (\ n -> Fin (Succ (Succ n)) -> *)
                                                                      (\ x -> m x)
                                                                      (\ _ _ _ -> Unit)
                                                                      n (FSucc (Succ n) (FSucc n f)))
                                                          (\ _ -> U)
                                                          (\ _ _ _ -> U)
                                                          n f )
                                           n f )
                      2 )
:: forall (m :: Bool -> *) . m False -> m True -> forall (b :: Bool) . m b
