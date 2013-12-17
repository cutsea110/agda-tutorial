module Sets.Records where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq


-- Record value definitions
record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ

x : R
x = record { r₁ = true ; r₂ = 2 }

-- Record value definitions with constructors
r : Bool → ℕ → R
r b n = record { r₁ = b ; r₂ = n }

x́ = r true 2

record Ŕ : Set where
  constructor ŕ
  field
    r₁ : Bool
    r₂ : ℕ

x″ = ŕ true 2

-- Field selectors
sel₁ : R → Bool
sel₁ = R.r₁

sel₂ : R → ℕ
sel₂ = R.r₂

x‴ = r (R.r₁ x) (R.r₂ x)

-- record vs. data

data R″ : Set where
  r″ : (r₁ : Bool) (r₂ : ℕ) → R″

r₁ : R″ → Bool
r₁ (r″ a b) = a

r₂ : R″ → ℕ
r₂ (r″ a b) = b

-- record is definitionally equivalent to its recombined parts
extRec : (x : R) → x ≡ r (R.r₁ x) (R.r₂ x)
extRec _ = Eq.refl

-- {- not possible -}
-- extData : (x : R″) → x ≡ r″ (r₁ x) (r₂ x)
-- extData _ = refl

record ⊤ : Set where

record _×_ (A B : Set) : Set where
  field
    inj₁ : A
    inj₂ : B

-- Dependent records

-- equivalent to List ℕ
open import Data.Vec using (Vec; []; _∷_)

record Listℕ : Set where
  constructor Lℕ
  field
    length : ℕ
    vector : Vec ℕ length

list : Listℕ
list = Lℕ 3 (0 ∷ 1 ∷ 2 ∷ [])

list́ : Listℕ
list́ = Lℕ _ (0 ∷ 1 ∷ 2 ∷ [])

length́ : Listℕ → ℕ
length́ = Listℕ.length

vectoŕ : (x : Listℕ) → Vec ℕ (length́ x) -- dependent
vectoŕ = Listℕ.vector

-- Parameterised record

record List (A : Set) : Set where
  constructor L
  field
    length : ℕ
    vector : Vec A length

list₂ : List Bool
list₂ = L _ (true ∷ false ∷ true ∷ [])

length″ : {A : Set} → List A → ℕ
length″ = List.length

vector″ : {A : Set} → (x : List A) → Vec A (length″ x) -- dependent
vector″ = List.vector


record ∑ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    inj₁ : A
    ibj₂ : B inj₁


-- Define the predicate of being an equivalence relation
record IsEquivalence {A : Set} (_≈_ : A → A → Set) : Set where
  field
    refl : ∀ {x} → x ≈ x
    sym : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

-- Prove that _≡_ is an equivalence relation on any set
isEquivalence : {A : Set} → IsEquivalence {A} _≡_
isEquivalence = record {refl = Eq.refl ; sym = Eq.sym ; trans = Eq.trans }


-- Define predicate of being a semigroup
-- Prove that ℕ is semigroup with _+_
record IsSemigroup {A : Set} (_⨁_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → x ⨁ (y ⨁ z) ≡ (x ⨁ y) ⨁ z

+-assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc zero y z = Eq.refl
+-assoc (suc x) y z = Eq.cong suc (+-assoc x y z)


open import Data.Nat.Properties

isSemigroup : IsSemigroup {ℕ} _+_
isSemigroup = record { assoc = +-assoc }
