module NatIf3 where

open import Data.Nat
open import Data.Vec

natIf3 : (a : Set) -> a -> a -> a -> ℕ -> a
natIf3 a x y z zero = x
natIf3 a x y z (suc zero) = y
natIf3 a x y z (suc (suc n)) = z

nilNat : Vec ℕ 0
nilNat = []

--test1 = natIf3 _ 1 nilNat 3 0

test2 = natIf3 _ nilNat 2 3 0
