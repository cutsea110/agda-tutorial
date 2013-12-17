module Modules.Parameterised where

open import Data.Nat

-- Module parameters
module X where
  module Y (x₁ : ℕ) where -- parameter
    y₁ = suc x₁  -- using then parameter
    y₂ = suc y₁

  x₂ = suc (suc (Y.y₁ 10)) -- filling in the parameter
  x₂́ = suc (Y.y₂ 10)

-- Module application
module X́ where
  module Y (x₁ : ℕ) where
    y₁ = suc x₁
    y₂ = suc y₁

  x₂ = suc (Y.y₂ 10)

  module Ý = Y 10 -- module application

  x₂́ = suc Ý.y₂ -- usage

-- Opening with module application
module X″ where
  module Y (x₁ : ℕ) where
    y₁ : ℕ -- but X″.Y.y₁ : (x₁ : ℕ) → ℕ from outside of this module
    y₁ = suc x₁
    y₂ : ℕ -- but X″.Y.y₂ : (x₁ : ℕ) → ℕ from outside of this module
    y₂ = suc y₁

  x₂ = suc (Y.y₂ 10)

  open module Ý = Y 10 -- opened module application

  x₂́ = suc y₂ -- usage
