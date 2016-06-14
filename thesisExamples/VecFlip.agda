module VecFlip where

open import AgdaPrelude


goodNil : Vec Nat Zero
goodNil = Nil Nat

badNil : Vec Zero Nat
badNil = Nil Nat
