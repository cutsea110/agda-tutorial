module Sets.With_Functions where

open import Data.Nat
open import Data.Empty using (⊥)
open import Data.List using (List; length)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

data Even : ℕ → Set where
  double : ∀ n → Even (n + n)

data Even' (m : ℕ) : Set where
  double : ∀ n → m ≡ n + n → Even' m

toEven : ∀ {m} → Even' m → Even m
toEven (double n refl) = double n

toEven' : ∀ {m} → Even m → Even' m
toEven' (double n) = double n refl
{--
toEven' (double zero) = double zero refl
toEven' (double (suc n)) = double (suc n) refl
--}

suc-+ : ∀ n m → suc (n + m) ≡ n + suc m
suc-+ zero m = refl
suc-+ (suc n) m = cong suc (suc-+ n m)

prev-≡ : ∀ {n m} → suc n ≡ suc m → n ≡ m
prev-≡ refl = refl

nextEven' : ∀ {n} → Even' n → Even' (suc (suc n))
nextEven' e = {!!}

prevEven' : ∀ {n} → Even' (suc (suc n)) → Even' n
prevEven' e = {!!}

¬Even'1 : Even' 1 → ⊥
¬Even'1 e = {!!}

isEven' : (n : ℕ) → Dec (Even' n)
isEven' n = {!!}

¬Even1 : ∀ {n} → Even n → n ≡ 1 → ⊥
¬Even1 e p = {!!}

nextEven : ∀ {n} → Even n → Even (suc (suc n))
nextEven e = {!!}

prevEven : ∀ {n} → Even (suc (suc n)) → Even n
prevEven e = {!!}

isEven : (n : ℕ) → Dec (Even n)
isEven n = {!!}

data _≤̈_ : ℕ → ℕ → Set where
  diff : ∀ i j → i ≤̈ j + i

infix 4 _≤̈_

data Vec (A : Set) : ℕ → Set where
  vec : (x : List A) → Vec A (length x)

