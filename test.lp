-- a simpler elimination scheme for natural numbers
let natFold =
  ( \ m mz ms -> natElim
                   _
                   mz
                   ( \ n' rec -> ms rec ) )
  :: forall (m :: *) . m -> (m -> m) -> Nat -> m
