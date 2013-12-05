module Sets.Parameters_vs_Indices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

data _∈_ {A : Set} (x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

data _⊆_ {A : Set} : List A → List A → Set where
  []⊆xs   : ∀ {xs} → [] ⊆ xs
  xs⊆xys  : ∀ {x xs ys} → xs ⊆ ys → xs ⊆ x ∷ ys
  xxs⊆xys : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

infix 4 _⊆_

test1 : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
test1 = xxs⊆xys (xxs⊆xys []⊆xs)

open import Data.Empty using (⊥)

test2 : 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] → ⊥
test2 (xs⊆xys (xs⊆xys ()))
test2 (xxs⊆xys (xs⊆xys ()))
test2 (xxs⊆xys (xxs⊆xys ()))
