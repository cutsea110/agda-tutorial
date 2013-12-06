module Functions.Functions_vs_Sets where

open import Sets.Enumerated using (Bool; true; false)

-- Negation as a relation
data Not : Bool → Bool → Set where
  n₁ : Not true false
  n₂ : Not false true

-- Negation as a function
not : Bool → Bool
not true = false
not false = true

