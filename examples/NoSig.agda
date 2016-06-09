module NoSig where

open import Data.Nat

myFun : ℕ
myFun = (\ x y -> y ) (\ x -> x) 0
