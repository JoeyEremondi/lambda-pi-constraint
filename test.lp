-- addition of natural numbers
let alwaysZero =
  ( \n ->
    natElim
      _
      (\n -> n)
      (\p rec n -> Succ (rec n))
      n ) :: Nat -> Nat -> Nat
