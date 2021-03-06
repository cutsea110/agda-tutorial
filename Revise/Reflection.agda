module Revise.Reflection where

open import Data.Nat using (ℕ; _+_; suc; zero; _≤_; s≤s; z≤n; _≟_)
open import Data.Vec using (Vec; []; _∷_; tail; head)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function renaming (_∘_ to _∘f_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- Syntax for existential quantification
ex : {A : Set} → (A → Set) → Set
ex = Σ _

syntax ex (λ y → x) = y ∣ x

-- Permutation relation _∼_
module _ {A : Set} where
  private V = Vec A
  infix 1 _∼_
  infixl 3 _∘_

  data _∼_ : ∀ {n} → V n → V n → Set where
    zero : [] ∼ []
    suc  : ∀ {n a} {xs ys : V n} → xs ∼ ys → a ∷ xs ∼ a ∷ ys
    _∘_  : ∀ {n} {xs ys zs : V n} → xs ∼ ys → ys ∼ zs → xs ∼ zs
    exch : ∀ {n a b} {xs : V n} → a ∷ b ∷ xs ∼ b ∷ a ∷ xs

  -- Reflexivity and symmetry of _∼_
  -- maybe this implementation beat auto proved code on performance.
  ∼-refl : ∀ {n} {xs : V n} → xs ∼ xs
  ∼-refl {xs = []} = zero
  ∼-refl {xs = _ ∷ []} = suc zero
  ∼-refl {xs = _ ∷ _ ∷ xs} = exch ∘ exch

  ∼-sym : ∀ {n} {xs ys : V n} → xs ∼ ys → ys ∼ xs
  ∼-sym zero = zero
  ∼-sym (suc p) = suc (∼-sym p)
  ∼-sym (p ∘ p₁) = ∼-sym p₁ ∘ ∼-sym p
  ∼-sym exch = exch

  _∘simp_ : ∀ {n} {xs ys zs : V n} → xs ∼ ys → ys ∼ zs → xs ∼ zs
  zero ∘simp a = a
  suc zero ∘simp a = a
  (exch ∘ exch) ∘simp a = a
  a ∘simp (exch ∘ exch) = a
  a ∘simp b = a ∘ b

  sucSimp : ∀ {n x} {xs ys : V n} → xs ∼ ys → x ∷ xs ∼ x ∷ ys
  sucSimp zero = suc zero
  sucSimp (suc zero) = exch ∘ exch
  sucSimp (exch ∘ exch) = exch ∘ exch
  sucSimp x = suc x

  -- Permutation relation _≈_
  infix 1 _≋_ _≈_
  infixr 3 _↪_
  infixr 4 _∷_

  data Into (n : ℕ) : Set where
    _↪_ : A → V n → Into n

  data _≋_ : ∀ {n} → Into n → V (suc n) → Set where
    zero : ∀ {n x} {xs : V n} → x ↪ xs ≋ x ∷ xs
    suc  : ∀ {n x y} {xs : V n} {ys} → x ↪ xs ≋ ys → x ↪ y ∷ xs ≋ y ∷ ys

  data _≈_ : ∀ {n} → V n → V n → Set where
    [] : [] ≈ []
    _∷_ : ∀ {n x} {xs ys : V n} {xxs} → x ↪ xs ≋ xxs → ys ≈ xs → x ∷ ys ≈ xxs

  -- Reflexivity of _≈_
  ≈-refl : ∀ {n} {xs : V n} → xs ≈ xs
  ≈-refl {xs = []} = []
  ≈-refl {xs = _ ∷ _} = zero ∷ ≈-refl

  -- _≈_ → _∼_
  ∼↪ : ∀ {n x} {xs : V n} {ys} → x ↪ xs ≋ ys → x ∷ xs ∼ ys
  ∼↪ zero = ∼-refl
  ∼↪ (suc e) = exch ∘simp sucSimp (∼↪ e)

  ≈→∼ : ∀ {n} {xs ys : V n} → xs ≈ ys → xs ∼ ys
  ≈→∼ [] = zero
  ≈→∼ (x ∷ e) = sucSimp (≈→∼ e) ∘simp ∼↪ x

  -- Transitivity of _≈_
  ↪-exch : ∀ {n x y} {xs : V n} {xxs yxxs} → x ↪ xs ≋ xxs → y ↪ xxs ≋ yxxs
           → yxs ∣ (y ↪ xs ≋ yxs) × (x ↪ yxs ≋ yxxs)
  ↪-exch zero zero = _ , zero , suc zero
  ↪-exch zero (suc b) = _ , b , zero
  ↪-exch (suc a) zero = _ , zero , suc (suc a)
  ↪-exch (suc a) (suc b) with ↪-exch a b
  ... | _ , s , t = _ , suc s , suc t

  getOut : ∀ {n x} {xs : V n} {xxs xys} → x ↪ xs ≋ xxs → xxs ≈ xys
           → ys ∣ (x ↪ ys ≋ xys) × (xs ≈ ys)
  getOut zero (x₁ ∷ b) = _ , x₁ , b
  getOut (suc a) (x₁ ∷ b) with getOut a b
  ... | (l , m , f) with ↪-exch m x₁
  ... | s , k , r = s , r , k ∷ f

  infixl 3 _∘≈_

  _∘≈_ : ∀ {n} {xs ys zs : V n} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  [] ∘≈ f = f
  x₁ ∷ e ∘≈ f with getOut x₁ f
  ... | a , b , c = b ∷ (e ∘≈ c)

  -- _∼_ → _≈_
  ∼→≈ : ∀ {n} {xs ys : V n} → xs ∼ ys → xs ≈ ys
  ∼→≈ zero = []
  ∼→≈ (suc e) = zero ∷ ∼→≈ e
  ∼→≈ (e ∘ e₁) = ∼→≈ e ∘≈ ∼→≈ e₁
  ∼→≈ exch = suc zero ∷ zero ∷ ≈-refl


  -- Symmetry of _≈_
  ≈-sym : ∀ {n} {xs ys : V n} → xs ≈ ys → ys ≈ xs
  ≈-sym a = ∼→≈ (∼-sym (≈→∼ a))

  -- Cancellation property of _≈_
  cancel : ∀ {n} {x} {xs ys : V n} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
  cancel (zero ∷ e) = e
  cancel (suc x₁ ∷ b ∷ e) = zero ∷ e ∘≈ b ∷ ≈-refl ∘≈ x₁ ∷ ≈-refl

t1 : 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] ≈ 3 ∷ 2 ∷ 4 ∷ 1 ∷ []
t1 = suc (suc (suc zero)) ∷ suc zero ∷ zero ∷ zero ∷ []
-- [] => [] ≈ []
-- zero ∷ [] => 4 ∷ [] ≈ 4 ∷ []
-- zero ∷ zero ∷ [] => 3 ∷ 4 ∷ [] ≈ 3 ∷ 4 ∷ []
-- suc zero ∷ zero ∷ zero ∷ [] => 2 ∷ 3 ∷ 4 ∷ [] ≈ 3 ∷ 2 ∷ 4 ∷ []
-- suc (suc (suc zero)) ∷ suc zero ∷ zero ∷ zero ∷ [] => 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] ≈ 3 ∷ 2 ∷ 4 ∷ 1 ∷ []
t2 : 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] ≈ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
t2 = suc (suc (suc zero)) ∷ suc (suc zero) ∷ suc zero ∷ zero ∷ []
-- [] => [] ≈ []
-- zero ∷ [] => 4 ∷ [] ≈ 4 ∷ []
-- suc zero ∷ zero ∷ [] => 3 ∷ 4 ∷ [] ≈ 4 ∷ 3 ∷ []
-- suc (suc zero) ∷ suc zero ∷ zero ∷ [] => 2 ∷ 3 ∷ 4 ∷ [] ≈ 4 ∷ 3 ∷ 2 ∷ []
-- suc (suc (suc zero)) ∷ suc (suc zero) ∷ suc zero ∷ zero ∷ [] => 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] ≈ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

f2 : 1 ∷ 2 ∷ [] ≈ 1 ∷ 1 ∷ [] → ⊥
f2 (zero ∷ () ∷ [])
f2 (suc x ∷ () ∷ [])

module _ {A : Set} ⦃ eq : Decidable {A = A} _≡_ ⦄ where

  private V = Vec A

  getOut' : ∀ {n} x (xs : V (suc n)) → Dec (ys ∣ x ↪ ys ≋ xs)
  getOut'  x  (x₁ ∷ xs) with eq x x₁
  getOut' .x₁ (x₁ ∷ xs) | yes refl = yes (xs , zero)
  getOut'  x  (x₁ ∷ []) | no ¬p = no (¬p ∘f f x refl) where
    f : ∀ a → x ≡ a → (ys ∣ a ↪ ys ≋ x₁ ∷ []) → x ≡ x₁
    f .x₁ k (.[] , zero) = k
  getOut'  x  (x₁ ∷ y ∷ xs) | no ¬p with getOut' x (y ∷ xs)
  ... | yes (a , b) = yes (x₁ ∷ a , suc b)
  ... | no ¬q = no (f x refl) where
    f : ∀ a → x ≡ a → (ys ∣ a ↪ ys ≋ x₁ ∷ y ∷ xs) → ⊥
    f .x₁ e (.(y ∷ xs) , zero) = ¬p e
    f a e (.x₁ ∷ xs , suc q) with a | e
    ... | .x | refl = ¬q (xs , q)

  infix 2 _≈?_

  _≈?_ : ∀ {n} → (xs ys : V n) → Dec (xs ≈ ys)
  [] ≈? [] = yes []
  x ∷ xs ≈? ys with getOut' x ys
  ... | no ¬p = no λ { (h ∷ _) → ¬p (_ , h)}
  ... | yes (zs , p) with xs ≈? zs
  ... | yes p' = yes (p ∷ p')
  ... | no ¬p = no λ e → ¬p (cancel (e ∘≈ ≈-sym (p ∷ ≈-refl)))

try = 1 ∷ 20 ∷ 3 ∷ 4 ∷ [] ≈? 3 ∷ 2 ∷ 4 ∷ 1 ∷ []

open import Reflection hiding (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
