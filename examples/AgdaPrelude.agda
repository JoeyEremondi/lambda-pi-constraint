{-#  OPTIONS --type-in-type #-}
module AgdaPrelude where

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

natElim : (m : Nat -> Set) -> (mz : m Zero) -> (ms : (l : Nat) -> m l -> m (Succ l)) -> (k : Nat) -> m k
natElim m mz ms Zero = mz
natElim m mz ms (Succ k) = ms k (natElim m mz ms k)

data Vec : Set -> Nat -> Set where
  Nil : (a : Set) -> Vec a Zero
  Cons : (a : Set) -> (n : Nat) -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

data Eq : (a : Set) -> a -> a -> Set where
  Refl : (a : Set) -> (x : a) -> Eq a x x
