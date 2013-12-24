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



infixr 5 _∷_
data Vec (A : Set) : (n : ℕ) → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)


infix 1 _∼_
infixl 3 _∘_
data _∼_ {A : Set} : ∀ {n} → Vec A n → Vec A n → Set where
  zero : [] ∼ []
  suc  : ∀ {n a} {xs ys : Vec A n} → xs ∼ ys → a ∷ xs ∼ a ∷ ys
  _∘_  : ∀ {n} {xs ys zs : Vec A n} → xs ∼ ys → ys ∼ zs → xs ∼ zs
  exch : ∀ {n a b} {xs : Vec A n} → a ∷ b ∷ xs ∼ b ∷ a ∷ xs

t0 : 1 ∷ 2 ∷ 3 ∷ [] ∼ 2 ∷ 3 ∷ 1 ∷ []
t0 = exch ∘ suc exch
-- _∘_ : 1 ∷ 2 ∷ 3 ∷ [] ∼ 2 ∷ 1 ∷ 3 ∷ [] → 2 ∷ 1 ∷ 3 ∷ [] ∼ 2 ∷ 3 ∷ 1 ∷ [] → 1 ∷ 2 ∷ 3 ∷ [] ∼ 2 ∷ 3 ∷ 1 ∷ []
--      |<-           exch            ->|   |<-          suc exch         ->|
t0' : 3 ∷ 2 ∷ 1 ∷ [] ∼ 2 ∷ 1 ∷ 3 ∷ []
t0' = exch ∘ suc exch

infixr 3 _↪_
data Into {A : Set} (n : ℕ) : Set where
  _↪_ : A → Vec A n → Into n

infix 1 _≋_
data _≋_ {A : Set} : ∀ {n} → Into {A} n → Vec A (suc n) → Set where
  zero : ∀ {n x} {xs : Vec A n} → x ↪ xs ≋ x ∷ xs
  suc  : ∀ {n x y} {xs : Vec A n} {ys} → x ↪ xs ≋ ys → x ↪ y ∷ xs ≋ y ∷ ys

infix 1 _≈_
infixr 4 _◂_
data _≈_ {A : Set} : ∀ {n} → Vec A n → Vec A n → Set where
  [] : [] ≈ []
  _◂_ : ∀ {n x} {xs ys : Vec A n} {xxs} → x ↪ xs ≋ xxs → ys ≈ xs → x ∷ ys ≈ xxs

t1 : 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] ≈ 3 ∷ 2 ∷ 4 ∷ 1 ∷ []
t1 = suc (suc (suc zero)) ◂ suc zero ◂ zero ◂ zero ◂ []
