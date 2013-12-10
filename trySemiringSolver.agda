module trySemiringSolver where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡-official_)

f : ∀ a b c → a + b * c + 1 ≡-official 1 + c * b + a
f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl
