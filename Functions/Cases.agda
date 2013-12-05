module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)

not : Bool → Bool
not true = false
not false = true

_∧_ : Bool → Bool → Bool
true ∧ y = y
false ∧ y = false

infixr 6 _∧_

_∨_ : Bool → Bool → Bool
true ∨ y = true
false ∨ y = y
