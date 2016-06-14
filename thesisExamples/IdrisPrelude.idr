module IdrisPrelude

%hide Prelude.Nat.Nat


data Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

natElim : (m : Nat -> Type) -> (mz : m Zero) -> (ms : (l : Nat) -> m l -> m (Succ l)) -> (k : Nat) -> m k
natElim m mz ms Zero = mz
natElim m mz ms (Succ k) = ms k (natElim m mz ms k)

data Vec : Type -> Nat -> Type where
  Nil : (a : Type) -> Vec a Zero
  Cons : (a : Type) -> (n : Nat) -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

data Eq : (a : Type) -> a -> a -> Type where
  Refl : (a : Type) -> (x : a) -> Eq a x x
