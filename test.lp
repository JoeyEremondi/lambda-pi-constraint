-- addition of natural numbers
let plus =
  natElim
    (\_ -> _)           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

let plusPf =
   (Refl _ _)
   :: Eq Nat 0 (plus 0 0)

let natFold =
  ( \ m mz ms -> natElim
                   ( \ _ -> Nat )
                   mz
                   ( \ n' rec -> ms rec ) )
  :: _
