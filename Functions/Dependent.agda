module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

_-_ : (n : ℕ) → Fin (suc n) → ℕ
zero - zero = zero
zero - suc ()
n - zero = n
suc n - suc m = n - m

ε = 3 - suc (suc (suc zero))
one = 4 - suc (suc (suc zero))
-- err = 3 - suc (suc (suc (suc zero)))

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = zero
toℕ (suc n) = suc (toℕ n)

t1 : 0 < 1 -- suc 0 ≤ 1 => 1 ≤ 1
t1 = s≤s z≤n

-- fromℕ≤ such that toℕ (fromℕ≤ e) is m if e : m < n
fromℕ≤ : ∀ {m n} → m < n → Fin n -- NOTE!: m < n => suc m ≤ n
fromℕ≤ (s≤s z≤n) = zero
fromℕ≤ (s≤s (s≤s m≤n)) = suc (fromℕ≤ (s≤s m≤n))

open import Relation.Binary.PropositionalEquality
t2 : toℕ (fromℕ≤ (s≤s (s≤s (s≤s (z≤n {1}))))) ≡ 2 -- 2 < 4 => 2
t2 = refl

{--
open import Data.Nat using (_≤_)
fromℕ≤' : ∀ {m n} → suc m ≤ n → Fin n
fromℕ≤' (s≤s z≤n) = zero
fromℕ≤' (s≤s (s≤s m≤n)) = suc (fromℕ≤' (s≤s m≤n))
--}

-- inject+ such that toℕ (inject+ n i) is the same as toℕ i
inject+ : ∀ {n} x → Fin n → Fin (n + x)
inject+ {zero} x ()
inject+ {suc n} x zero = zero
inject+ {suc n} x (suc fn) = suc (inject+ {n} x fn)

-- four such that toℕ four is 4
four : Fin 66
four = inject+ {66} zero (suc (suc (suc (suc zero))))

t3 : toℕ four ≡ 4
t3 = refl

-- raise such that toℕ (raise n i) is the same as n + toℕ i
raise : ∀ {n} x → Fin n → Fin (x + n)
raise {n} zero fn = fn
raise {n} (suc x) fn = suc (raise {n} x fn)

t4 : ∀ {m n i} → toℕ (raise {m} n i) ≡ n + toℕ i
t4 {n = zero} = refl
t4 {n = suc n} {i} = cong suc (t4 {n = n})

head : ∀ {n} {A : Set} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : ∀ {n} {A : Set} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

_++_ : ∀ {n m} {A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

maps : ∀ {n} {A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = []
maps (f ∷ fs) (x ∷ xs) = f x ∷ maps fs xs

replicate : ∀ {n} {A : Set} → A → Vec A n
replicate {zero} x = []
replicate {suc n} x = x ∷ replicate {n} x

map : ∀ {n} {A B : Set} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

zip : ∀ {n} {A B : Set} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

_!_ : ∀ {n} {A : Set} → Vec A n → Fin n → A
(x ∷ xs) ! zero = x
(x ∷ xs) ! suc n = xs ! n
