module Functions.Large where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

_≤'_ : ℕ → ℕ → Set
zero ≤' n = ⊤
suc m ≤' zero = ⊥
suc m ≤' suc n = m ≤' n

f : {n m : ℕ} → n ≤ m → n ≤ suc m
f z≤n = z≤n
f (s≤s p) = s≤s (f p)

f' : {n m : ℕ} → n ≤' m → n ≤' suc m
f' {zero} p = tt
f' {suc n} {zero} ()
f' {suc n} {suc m} p = f' {n} {m} p

data _≡_ (x : ℕ) : ℕ → Set where
  refl : x ≡ x

_≡'_ : (x : ℕ) → ℕ → Set
zero ≡' zero = ⊤
zero ≡' suc y = ⊥
suc x ≡' zero = ⊥
suc x ≡' suc y = x ≡' y

data _≢_ : ℕ → ℕ → Set where
  z≢s : {n : ℕ} → zero ≢ suc n
  s≢z : {n : ℕ} → suc n ≢ zero
  s≢s : {n m : ℕ} → n ≢ m → suc n ≢ suc m

_≢'_ : ℕ → ℕ → Set
zero ≢' zero = ⊥
zero ≢' suc y = ⊤
suc x ≢' zero = ⊤
suc x ≢' suc y = x ≢ y

data Even : ℕ → Set where
  evenZZ : Even zero
  evenSS : {n : ℕ} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  oddOO : Odd (suc zero)
  oddSS : {n : ℕ} → Odd n → Odd (suc (suc n))

Even' : ℕ → Set
Even' zero = ⊤
Even' (suc zero) = ⊥
Even' (suc (suc n)) = Even' n

Odd' : ℕ → Set
Odd' zero = ⊥
Odd' (suc zero) = ⊤
Odd' (suc (suc n)) = Odd' n

-- Macro-like Set definitions
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

Maybe : Set → Set
Maybe A = ⊤ ⊎ A -- but we can't distinguish Maybe ⊤ from ⊤ ⊎ ⊤

_>_ : ℕ → ℕ → Set
n > m = {!n ≥ (suc m)!}

_≥_ : ℕ → ℕ → Set
zero ≥ zero = ⊤
zero ≥ suc m = ⊥
suc n ≥ zero = ⊤
suc n ≥ suc m = n ≥ m

_≤′_ : ℕ → ℕ → Set
zero ≤′ zero = ⊤
zero ≤′ suc m = ⊤
suc n ≤′ zero = ⊥
suc n ≤′ suc m = n ≤′ m

¬ : Set → Set
¬ A = A → ⊥

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

Fin₀ : ℕ → Set
Fin₀ zero = ⊥
Fin₀ (suc n) = ⊤ ⊎ Fin₀ n
