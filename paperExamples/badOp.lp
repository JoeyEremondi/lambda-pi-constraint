-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ


let myOp = ( (\ _ -> 0 ) :: Vec Nat 0 -> Nat)


let myApp = (\ _ -> \ _ -> \ f -> \ a -> f a ) :: forall A :: * . forall B :: * . (A -> B) -> A -> B

let x = myApp _ _ myOp 0

