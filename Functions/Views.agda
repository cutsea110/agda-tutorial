module Functions.Views where

open import Data.Nat using (ℕ; zero; suc; _<_; _>_; s≤s; z≤n; _+_; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  zero : Even zero
  odd : ∀ {n} → Odd n → Even (suc n)

data Odd where
  even : ∀ {n} → Even n → Odd (suc n)

parity : ∀ n → Even n ⊎ Odd n
parity zero = inj₁ zero
parity (suc n) with parity n
parity (suc n) | inj₁ x = inj₂ (even x)
parity (suc n) | inj₂ y = inj₁ (odd y)

ordering : ∀ n m → n < m ⊎ n ≡ m ⊎ n > m
ordering zero zero = inj₂ (inj₁ refl)
ordering zero (suc m) = inj₁ (s≤s z≤n)
ordering (suc n) zero = inj₂ (inj₂ (s≤s z≤n))
ordering (suc n) (suc m)  = {!!}

data Parity : ℕ → Set where
  even : ∀ n → Parity (n * 2)
  odd  : ∀ n → Parity (1 + n * 2)

data Ordering : ℕ → ℕ → Set where
  less : ∀ m k → Ordering m (suc (m + k))
  equal : ∀ m → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

parity' : ∀ n → Parity n
parity' n = {!!}

compare : ∀ m n → Ordering m n
compare m n = {!!}

⌊_/2⌋ : ℕ → ℕ
⌊ n /2⌋ = {!!}
