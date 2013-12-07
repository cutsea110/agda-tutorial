module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (flip; _$_; _∘_)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n q = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

total : ∀ m n → m ≤ n ⊎ n ≤ m
total zero n = inj₁ z≤n
total m zero = inj₂ z≤n
total (suc m) (suc n) with total m n
total (suc m) (suc n) | inj₁ x = inj₁ (s≤s x)
total (suc m) (suc n) | inj₂ y = inj₂ (s≤s y)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s p) = p

≤-mono : ∀ {m n k} → n ≤ m → k + n ≤ k + m
≤-mono {m} {n} {zero} p = p
≤-mono {m} {n} {suc k} p = s≤s (≤-mono {m} {n} {k} p)

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤́⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
≤́⇒≤ {a} .{a} ≤′-refl = m≤m a
  where
    m≤m : (m : ℕ) → m ≤ m
    m≤m zero = z≤n
    m≤m (suc m) = s≤s (m≤m m)
≤́⇒≤ {a} {suc b} (≤′-step p) = ≤-step (≤́⇒≤ p)

z≤́n : ∀ n → zero ≤′ n
z≤́n zero = ≤′-refl
z≤́n (suc n) = ≤′-step (z≤́n n)

s≤́s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤́s ≤′-refl = ≤′-refl
s≤́s (≤′-step p) = ≤′-step (s≤́s p)

≤⇒≤́ : ∀ {a b} → a ≤ b → a ≤′ b
≤⇒≤́ {zero} {b} p = z≤́n b
≤⇒≤́ {suc a} {zero} ()
≤⇒≤́ {suc a} {suc b} (s≤s p) = s≤́s (≤⇒≤́ p)

fin≤ : ∀ {n} (m : Fin n) → toℕ m < n
fin≤ {zero} ()
fin≤ {suc n} zero = s≤s z≤n
fin≤ {suc n} (suc m) = s≤s (fin≤ m)
