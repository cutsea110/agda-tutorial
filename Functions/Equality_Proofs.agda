module Functions.Equality_Proofs where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

refl' : ∀ {A} (a : A) → a ≡ a
refl' a = refl

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = refl

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc $ +-right-identity n

+-left-identity : ∀ n → 0 + n ≡ n
+-left-identity n = refl

+-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc $ +-assoc a b c

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc $ m+1+n≡1+m+n m n

mutual
  1+m+n≡m+1+n : ∀ m n → suc (m + n) ≡ n + suc m
  1+m+n≡m+1+n m zero = cong suc $ +-right-identity m
  1+m+n≡m+1+n m (suc n) = cong suc $ m+Sn≡n+Sm m n

  m+Sn≡n+Sm : ∀ m n → m + suc n ≡ n + suc m
  m+Sn≡n+Sm m n = trans (m+1+n≡1+m+n m n) (1+m+n≡m+1+n m n)

-- see the definition of +-comm' below
+-commutativity : ∀ a b → a + b ≡ b + a
+-commutativity zero b = sym $ +-right-identity b
+-commutativity (suc a) zero = cong suc $ +-right-identity a
+-commutativity (suc a) (suc b) = cong suc $ m+Sn≡n+Sm a b

fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc $ fromList xs

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

from-to : ∀ a → fromList (toList a) ≡ a
from-to zero = refl
from-to (suc n) = cong suc (from-to n)

to-from : ∀ a → toList (fromList a) ≡ a
to-from [] = refl
to-from (tt ∷ xs) = cong (_∷_ tt) (to-from xs)

fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
fromPreserves++ [] ys = refl
fromPreserves++ (x ∷ xs) ys = cong suc (fromPreserves++ xs ys)

toPreserves+ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
toPreserves+ zero n = refl
toPreserves+ (suc m) n = cong (_∷_ tt) (toPreserves+ m n)

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix 2 _∎

+-comm' : (n m : ℕ) → n + m ≡ m + n
+-comm' zero n = sym (+-right-identity n)
+-comm' (suc m) n =
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm' m n) ⟩
    suc (n + m)
  ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
    n + suc m
  ∎

*-+-distr-l : ∀ a b c → a * c + b * c ≡ (a + b) * c
*-+-distr-l zero y z = refl
*-+-distr-l (suc x) y z =
    (z + (x * z)) + (y * z)
  ≡⟨ sym (+-assoc z (x * z) (y * z)) ⟩
    z + ((x * z) + (y * z))
  ≡⟨ cong (_+_ z) (*-+-distr-l x y z) ⟩
    z + (x + y) * z
  ∎

*-assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-assoc zero y z = refl
*-assoc (suc x) y z =
    y * z + x * (y * z)
  ≡⟨ cong (λ a → y * z + a) (*-assoc x y z) ⟩
    y * z + (x * y) * z
  ≡⟨ *-+-distr-l y (x * y) z ⟩
    (y + x * y) * z
  ∎

*-left-identity : ∀ a → 1 * a ≡ a
*-left-identity n = +-right-identity n

*-right-identity : ∀ a → a * 1 ≡ a
*-right-identity zero = refl
*-right-identity (suc n) = cong suc (*-right-identity n)

n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 zero = refl
n*0≡0 (suc n) = n*0≡0 n

*-+-distr-r : ∀ a b c → a * b + a * c ≡ a * (b + c)
*-+-distr-r zero y z = refl
*-+-distr-r (suc x) y zero =
    (y + x * y) + x * 0
  ≡⟨ cong (λ a → y + x * y + a) (n*0≡0 x) ⟩
    (y + x * y) + 0
  ≡⟨ sym (+-assoc y (x * y) zero) ⟩
    y + (x * y + 0)
  ≡⟨ cong (_+_ y) (+-comm' (x * y) zero) ⟩
    y + (0 + x * y)
  ≡⟨ +-assoc y zero (x * y) ⟩
    y + 0 + x * y
  ≡⟨ cong (λ a → y + 0 + a) (cong (_*_ x) (sym (+-right-identity y))) ⟩
    y + 0 + x * (y + 0)
  ∎
*-+-distr-r (suc x) y (suc z) =
    (y + x * y) + suc (z + x * suc z)
  ≡⟨ cong (_+_ (y + x * y)) (1+m+n≡m+1+n z (x * suc z)) ⟩
    (y + x * y) + (x * suc z + suc z)
  ≡⟨ sym (+-assoc y (x * y) (x * suc z + suc z)) ⟩
    y + (x * y + (x * suc z + suc z))
  ≡⟨ cong (_+_ y) (+-assoc (x * y) (x * suc z) (suc z)) ⟩
    y + ((x * y + x * suc z) + suc z)
  ≡⟨ cong (_+_ y) (+-comm' (x * y + x * suc z) (suc z)) ⟩
    y + (suc z + (x * y + x * suc z))
  ≡⟨ +-assoc y (suc z) (x * y + x * suc z) ⟩
    y + suc z + (x * y + x * suc z)
  ≡⟨ cong (_+_ (y + suc z)) (*-+-distr-r x y (suc z)) ⟩
    y + suc z + x * (y + suc z)
  ∎

n*Sm≡n+n*m : ∀ n m → n * suc m ≡ n + n * m
n*Sm≡n+n*m n m =
    n * suc m
  ≡⟨ refl ⟩
    n * (1 + m)
  ≡⟨ sym (*-+-distr-r n (suc zero) m) ⟩
    n * 1 + n * m
  ≡⟨ cong (λ a → a + n * m) (*-right-identity n) ⟩
    n + n * m
  ∎

*-suc : ∀ n m → n + n * m ≡ n * suc m
*-suc zero m = refl
*-suc (suc n) m = cong suc (sym (m+n*Sm≡n+m+n*m n m))
  where
    m+n*Sm≡n+m+n*m : ∀ n m → m + n * suc m ≡ n + (m + n * m)
    m+n*Sm≡n+m+n*m n m =
        m + (n * suc m)
      ≡⟨ cong (_+_ m) (n*Sm≡n+n*m n m) ⟩
        m + (n + n * m)
      ≡⟨ +-assoc m n (n * m) ⟩
        (m + n) + n * m
      ≡⟨ cong (λ a → a + n * m) (+-comm' m n) ⟩
        (n + m) + n * m
      ≡⟨ sym (+-assoc n m (n * m)) ⟩
        n + (m + n * m)
      ∎

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = sym (n*0≡0 n)
*-comm (suc m) n =
    n + m * n
  ≡⟨ cong (_+_ n) (*-comm m n) ⟩
    n + n * m
  ≡⟨ *-suc n m ⟩
    n * suc m
  ∎
