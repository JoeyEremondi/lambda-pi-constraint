

let nat1Elim =
  ( \ m m0 m1 ms -> natElim m m0
                            (\ p rec -> natElim (\ n -> m (Succ n)) m1 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 ->
     (forall n :: Nat . m (Succ n) -> m (Succ (Succ n))) ->
     forall (n :: Nat) . m n

-- unit type
--let Unit = Fin 1
-- constructor
--let U = FZero 0

{-

-- eliminator
let unitElim =
  ( \ m mu -> finElim ( nat1Elim (\ n -> Fin n -> *)
                                 (\ _ -> Unit)
                                 (\ x -> m x)
                                 (\ _ _ _ -> Unit) )
                      ( natElim (\ n -> natElim (\ n -> Fin (Succ n) -> *)
                                                (\ x -> m x)
                                                (\ _ _ _ -> Unit)
                                                n (FZero n))
                                mu
                                (\ _ _ -> U) )
                      ( \ n f _ -> finElim (\ n f -> natElim (\ n -> Fin (Succ n) -> *)
                                                             (\ x -> m x)
                                                             (\ _ _ _ -> Unit)
                                                             n (FSucc n f))
                                           (\ _ -> U)
                                           (\ _ _ _ -> U)
                                           n f )
                      1 )
  :: forall (m :: Unit -> *) . m U -> forall (u :: Unit) . m u
-}
