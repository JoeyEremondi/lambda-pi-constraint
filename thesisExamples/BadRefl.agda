{-#  OPTIONS --type-in-type #-}
module BadRefl where

--open import Relation.Binary.PropositionalEquality

open import Data.Nat

Nat = ℕ
Zero = 0
Succ = suc

data Eq : (a : Set) -> a -> a -> Set where
  Refl : (a : Set) -> (x : a) -> Eq a x x

badRefl :  Eq (Nat -> Nat) (\x -> x) (\x -> Zero)
badRefl = (Refl _ (\x -> x))
