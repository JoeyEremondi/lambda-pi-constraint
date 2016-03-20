-- addition of natural numbers

let plus =
  (\n -> natElim
      _           -- motive
      ( \ n -> n )
      ( \ p rec n -> Succ (rec n) ) n) :: _

{-
let plusPf =
   (Refl _ _)
   :: Eq Nat 0 (plus 0 0)




let natFold =
  ( \ m mz ms -> natElim
                   ( \ _ -> _ )
                   mz
                   ( \ n' rec -> ms rec ) )
  :: forall (m :: *) . m -> (m -> m) -> Nat -> m
-}
