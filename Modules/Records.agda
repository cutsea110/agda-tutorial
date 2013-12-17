module Modules.Records where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ

x : R
x = record { r₁ = true ; r₂ = 2 }

module SimpleOpening where

  open R -- brings r₁ and r₂ into scope

  y : Bool
  y = r₁ x

module AppliedOpening where

  open R x -- brings r₁ and r₂ into scope, first parameter filled in


  y : Bool
  y = r₁


module AppliedOpeninǵ where

  y : Bool
  y = r₁ where open R x
