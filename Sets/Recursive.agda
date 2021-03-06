module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data ℕ⁺ : Set where
  one      : ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂
  id   : ℕ⁺ → ℕ₂

-- This is like newtype in Haskell
{--
data ℕ́ : Set where
  cast : ℕ → ℕ́
--}

