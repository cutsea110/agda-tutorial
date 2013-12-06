module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)
infixl 6 _+_

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n

infixl 6 _⊔_
_⊔_ : ℕ → ℕ → ℕ
m ⊔ n with m ∸ n
m ⊔ n | zero = n
m ⊔ n | suc l = m

infixl 7 _⊓_
_⊓_ : ℕ → ℕ → ℕ
m ⊓ n with m ∸ n
m ⊓ n | zero = m
m ⊓ n | suc l = n

⌊_/2⌋ : ℕ → ℕ
⌊ zero /2⌋ = zero
⌊ suc zero /2⌋ = zero
⌊ suc (suc n) /2⌋ = ⌊ n /2⌋ + suc zero


odd : ℕ → Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

_≡?_ : ℕ → ℕ → Bool
m ≡? n with m ∸ n | n ∸ m
m ≡? n | zero | zero = true
m ≡? n | x | y = false

_≤?_ : ℕ → ℕ → Bool
zero ≤? n = true
m ≤? zero = false
suc m ≤? suc n = m ≤? n


open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)

from : ℕ₂ → ℕ
from zero = zero
from (id one) = suc zero
from (id (double n)) = (suc (suc zero)) * from (id n)
from (id (double+1 n)) = suc (suc zero) * from (id n) + suc zero

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

mirror : BinTree → BinTree
mirror leaf = leaf
mirror (node l r) = node (mirror r) (mirror l)
