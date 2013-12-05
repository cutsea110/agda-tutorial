module Sets.Parametric where

open import Data.Nat

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  [] : List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ (A B : Set) where
  _∷_ : B → List₁ A B → List₂ A B

data AlterList (A B : Set) : Set where
  [] : AlterList A B
  _∷_ : A → AlterList B A → AlterList A B

data T4 (A : Set) : Set where
  quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
  zero : A → Square A
  suc  : Square (T4 A) → Square A
