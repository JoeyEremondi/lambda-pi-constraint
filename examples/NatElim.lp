let alwaysZero =
  natElim
    ( \ _ -> _)           -- motive
    ( 0 )                    -- case for Zero
    ( \ _ _ -> 0 )   -- case for Succ
