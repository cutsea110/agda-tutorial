module Application.Algebra where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)

import Relation.Binary.EqReasoning as EqR

-- Semigroup property
record IsSemigroup {A : Set} (_∙_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc zero y z = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)

ℕ+-isSemigroup : IsSemigroup _+_
ℕ+-isSemigroup = record { assoc = +-assoc }

module Usage₁ where
  open IsSemigroup
  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = +-assoc n (suc zero) (suc zero)

module Usage₂ where
  open IsSemigroup ℕ+-isSemigroup
  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n (suc zero) (suc zero)

module Usage₃ where
  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n (suc zero) (suc zero)
    where open IsSemigroup ℕ+-isSemigroup

-- Monoid property
record IsMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identity    : (∀ x → ε ∙ x ≡ x) × (∀ x → x ∙ ε ≡ x)

  open IsSemigroup isSemigroup public

+-identity : (∀ x → 0 + x ≡ x) × (∀ x → x + 0 ≡ x)
+-identity = (λ n → refl) , n+0≡n
  where
    n+0≡n : ∀ n → n + 0 ≡ n
    n+0≡n zero = refl
    n+0≡n (suc n) = cong suc (n+0≡n n)

ℕ+0-isMonoid : IsMonoid _+_ 0
ℕ+0-isMonoid = record { isSemigroup = ℕ+-isSemigroup ; identity = +-identity }

module Usage₄ where
  ex : ∀ n → (n + 0) + n ≡ n + n
  ex n = cong (λ x → x + n) (proj₂ identity n)
    where open IsMonoid ℕ+0-isMonoid

  ex́ : ∀ n → (n + 0) + n ≡ n + n
  ex́ n = assoc n 0 n
    where open IsMonoid ℕ+0-isMonoid

-- Named binary operaters
Op₂ : Set → Set
Op₂ A = A → A → A

record IsSemigrouṕ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

Op₁ : Set → Set
Op₁ A = A → A

-- Named function properties
Associative : {A : Set} → Op₂ A → Set
Associative _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record IsSemigroup″ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc : Associative _∙_

Commutative : {A : Set} → Op₂ A → Set _
Commutative _∙_ = ∀ x y → x ∙ y ≡ y ∙ x

LeftIdentity : {A : Set} → A → Op₂ A → Set _
LeftIdentity ε _∙_ = ∀ x → ε ∙ x ≡ x

RightIdentity : {A : Set} → A → Op₂ A → Set _
RightIdentity ε _∙_ = ∀ x → x ∙ ε ≡ x

Identity : {A : Set} → A → Op₂ A → Set _
Identity ε _∙_ = LeftIdentity ε _∙_ × RightIdentity ε _∙_

-- Commutative monoid property
record IsCommutativeMonoid́ {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isMonoid : IsMonoid _∙_ ε
    comm     : Commutative _∙_

record IsCommutativeMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identityˡ   : LeftIdentity ε _∙_
    comm        : Commutative _∙_

  open IsSemigroup isSemigroup public

  identity : Identity ε _∙_
  identity = identityˡ , identityʳ
    where
    open EqR (setoid A)

    identityʳ : RightIdentity ε _∙_
    identityʳ = λ x → begin
      (x  ∙ ε) ≈⟨ comm x ε ⟩
      (ε ∙  x) ≈⟨ identityˡ x ⟩
      x ∎

  isMonoid : IsMonoid _∙_ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity    = identity
    }

LeftInverse : {A : Set} → A → Op₂ A  → Op₁ A → Set _
LeftInverse ε _∙_ _⁻¹ = ∀ x → x ⁻¹ ∙ x ≡ ε

RightInverse : {A : Set} → A → Op₂ A → Op₁ A → Set _
RightInverse ε _∙_ _⁻¹ = ∀ x → x ∙ x ⁻¹ ≡ ε

record IsGroup {A : Set} (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set where
  field
    isMonoid : IsMonoid _∙_ ε
    isInverse  : LeftInverse ε _∙_ _⁻¹ × RightInverse ε _∙_ _⁻¹

  open IsMonoid isMonoid public


record IsAbelianGroup {A : Set} (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set where
  field
    isGroup : IsGroup _∙_ ε _⁻¹
    comm    : Commutative _∙_

  open IsGroup isGroup public


-- The type of all semigroups
record Semigroup : Set₁ where
  infixl 7 _∙_
  field
    Carrier : Set
    _∙_ : Op₂ Carrier
    isSemigroup : IsSemigroup _∙_

  open IsSemigroup isSemigroup public

ℕ+-isSemigrouṕ : Semigroup
ℕ+-isSemigrouṕ = record { Carrier = ℕ
                         ; _∙_ = _+_
                         ; isSemigroup = ℕ+-isSemigroup
                         }

record Monoid : Set₁ where
  infixl 7 _∙_
  field
    Carrier : Set
    ε : Carrier
    _∙_ : Op₂ Carrier
    isMonoid : IsMonoid _∙_ ε

  open IsMonoid isMonoid public

-- Some defined operations
module MonoidOperations (m : Monoid) where

  open Monoid m

  infixr 7 _x́_

  _x́_ : ℕ → Carrier → Carrier
  zero x́ y = ε
  (suc x) x́ y = y ∙ (x x́ y)


-- See standard library
import Algebra.FunctionProperties using (Op₁; Op₂)
import Algebra.FunctionProperties using (Associative; Commutative; LeftIdentity; RightIdentity; Identity)
import Algebra.Structures using (IsSemigroup; IsMonoid; IsCommutativeMonoid)
import Algebra using (Semigroup; Monoid; CommutativeMonoid)
import Algebra.Operations
import Data.Nat.Properties using (isCommutativeSemiring)

module StdLibUsage where
  open import Algebra.Structures as A using (IsCommutativeMonoid)
  open import Data.Nat.Properties using (isCommutativeSemiring)

  open A.IsCommutativeSemiring
  open A.IsCommutativeMonoid (+-isCommutativeMonoid isCommutativeSemiring)

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1
