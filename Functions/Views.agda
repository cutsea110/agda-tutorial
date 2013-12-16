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

ordering : ∀ n m → (n < m) ⊎ (n ≡ m) ⊎ (n > m)
ordering zero zero = inj₂ (inj₁ refl)
ordering zero (suc m) = inj₁ (s≤s z≤n)
ordering (suc n) zero = inj₂ (inj₂ (s≤s z≤n))
ordering (suc n) (suc m) with ordering n m
ordering (suc n) (suc m) | inj₁ x = inj₁ (s≤s x)
ordering (suc .m) (suc m) | inj₂ (inj₁ refl) = inj₂ (inj₁ refl)
ordering (suc .(suc n)) (suc m) | inj₂ (inj₂ (s≤s {.m} {n} y)) = inj₂ (inj₂ (s≤s (s≤s y)))

data Parity : ℕ → Set where
  even : ∀ n → Parity (n * 2)
  odd  : ∀ n → Parity (1 + n * 2)

data Ordering : ℕ → ℕ → Set where
  less : ∀ m k → Ordering m (suc (m + k))
  equal : ∀ m → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

parity' : ∀ n → Parity n
parity' zero = even zero
parity' (suc zero) = odd zero
parity' (suc (suc n)) with parity' n
parity' (suc (suc .(n * 2))) | even n = even (suc n)
parity' (suc (suc .(suc (n * 2)))) | odd n = odd (suc n)

compare : ∀ m n → Ordering m n
compare zero zero = equal zero
compare zero (suc n) = less zero n
compare (suc m) zero = greater zero m
compare (suc m) (suc n) with compare m n
compare (suc m) (suc .(suc (m + k))) | less .m k = less (suc m) k
compare (suc .n) (suc n) | equal .n = equal (suc n)
compare (suc .(suc (n + k))) (suc n) | greater .n k = greater (suc n) k

⌊_/2⌋ : ℕ → ℕ
⌊ zero /2⌋ = zero
⌊ suc n /2⌋ = n

data Mod4 : ℕ → Set where
  zero  : ∀ k → Mod4 ((k * 2) * 2)
  one   : ∀ k → Mod4 (1 + ((k * 2) * 2))
  two   : ∀ k → Mod4 ((1 + k * 2) * 2)
  three : ∀ k → Mod4 (1 + ((1 + k * 2) * 2))

mod4 : ∀ n → Mod4 n
mod4 n with parity' n
mod4 .(n * 2) | even n with parity' n
mod4 .(n * 2 * _) | even .(n * 2) | even n = zero n
mod4 .(suc (n * 2) * _) | even .(suc (n * 2)) | odd n = two n
mod4 .(suc (n * 2)) | odd n with parity' n
mod4 .(suc (n * 2 * _)) | odd .(n * 2) | even n = one n
mod4 .(suc (suc (n * 2) * _)) | odd .(suc (n * 2)) | odd n = three n
