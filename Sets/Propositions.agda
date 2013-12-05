module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt


data _≤_ : ℕ → ℕ → Set where
  z≰n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

0≤1 : 1 ≤ 10
0≤1 = s≤s z≰n

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

8≤4 : 8 ≤ 4 → ⊥
8≤4 (s≤s p) = 7≰3 p


data _≤'_ : ℕ → ℕ → Set where
  ≤'-refl : {m : ℕ} → m ≤' m
  ≤'-step : {m : ℕ} → {n : ℕ} → m ≤' n → m ≤' suc n

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k
