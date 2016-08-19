module BadRefl where

open import AgdaPrelude

plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

-- the other direction requires induction on N:
postulate pNPlus0isN : (n : Nat) -> Eq Nat (plus n Zero) n


-- the other direction requires induction on N:
succPlus : (n : Nat) -> Eq Nat  (Succ n) (plus (Succ n) Zero)
succPlus =
  (\n -> pNPlus0isN (Succ n))
