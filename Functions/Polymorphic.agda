module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ (toList n)

open import Relation.Binary.PropositionalEquality

prf : ∀{xs ys} → fromList (xs ++ ys) ≡ fromList xs + fromList ys
prf {[]} {ys} = refl
prf {x ∷ xs} {ys} = cong suc (prf {xs} {ys})

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

head : {A : Set} → List A → Maybe A
head [] = nothing
head (x ∷ xs) = just x
tail : {A : Set} → List A → Maybe (List A)
tail [] = nothing
tail (x ∷ xs) = just xs

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

maps : {A B : Set} → List (A → B) → List A → List B
maps []  _ = []
maps _  [] = []
maps (f ∷ fs) (x ∷ xs) = f x ∷ maps fs xs

⟨_⟩ : {A : Set} → A → List A
⟨ x ⟩ = x ∷ []

id : {A : Set} → A → A
id a = a

aNumber = id {ℕ} (suc zero)

const : {A B : Set} → A → B → A
const x _ = x

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f x y = f y x

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_
infixr 2 _×_

swap : {A B : Set} → A × B → B × A
swap (x , y) = y , x

proj₁ : {A B : Set} → A × B → A
proj₁ (x , _) = x
proj₂ : {A B : Set} → A × B → B
proj₂ (_ , y) = y

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
infixr 1 _⊎_

swap+ : {A B : Set} → A ⊎ B → B ⊎ A
swap+ (inj₁ x) = inj₂ x
swap+ (inj₂ x) = inj₁ x

⟨_,_⟩ : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⟨ f , _ ⟩ (inj₁ x) = f x
⟨ _ , g ⟩ (inj₂ x) = g x
