module Functions.Views.Decidability where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_; ≤-pred)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (const; _$_; _∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; subst; cong)
open PropEq.≡-Reasoning

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

1<2 : Dec (1 < 2)
1<2 = yes (s≤s (s≤s z≤n))

1≡1 : Dec (1 ≡ 1)
1≡1 = yes refl

1≡2 : Dec (1 ≡ 2)
1≡2 = no 1≡2' -- no (λ ())
  where
    1≡2' : 1 ≡ 2 → ⊥
    1≡2' ()

1>2 : Dec (1 > 2)
1>2 = no 3≤1
  where
    3≤1 : 3 ≤ 1 → ⊥
    3≤1 (s≤s ())

_≟_ : (a b : ℕ) → Dec (a ≡ b)
zero ≟ zero = yes refl
zero ≟ suc y = no 0≡Sn -- no (λ ())
  where
    0≡Sn : ∀ {x} → 0 ≡ suc x → ⊥
    0≡Sn ()
suc x ≟ zero = no Sn≡0 -- no (λ ())
  where
    Sn≡0 : ∀ {x} → suc x ≡ 0 → ⊥
    Sn≡0 ()
suc x ≟ suc y with x ≟ y
... | yes x≡y = yes (cong suc x≡y)
... | no x≢y = no (x≢y ∘ cong pred)

_≤?_ : (a b : ℕ) → Dec (a ≤ b)
zero ≤? y = yes z≤n
suc x ≤? zero = no (λ ())
suc x ≤? suc y with x ≤? y
... | yes x≤y = yes (s≤s x≤y)
... | no x≰y = no (x≰y ∘ ≤-pred)

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false
