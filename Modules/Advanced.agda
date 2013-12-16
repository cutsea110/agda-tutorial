module Modules.Advanced where

open import Data.Nat

-- Nested modules
module X where
  x₁ = 10

  module Y where
    y₁ = 11

    module Z where
      z = 12

    y₂ = 13

  x₂ = 14

-- Qualified names
module X́ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z  -- qualified name

  x₂ = suc Y.y₂
  x₂́ = suc (suc Y.Z.z)

-- Opening a module
module X″ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

    open Z -- open declaration

    y₂́ = suc z

  x₂ = suc Y.y₂
  -- x₂́ = suc (suc Y.z) -- not allowed

-- Public opening (re-exporting)
module X‴ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

    open Z public -- public opening

    y₂́ = suc z

  x₂ = suc Y.y₂
  x₂́ = suc (suc Y.z)

-- Private definitions
module X⁗ where
  x₁ = 10

  module Y where
    private
      y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

  x₂ = suc Y.y₂
  -- x₂́ = suc (suc (suc Y.y₁)) -- not accessible

-- Partial opening
module X⁵ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      ź = z
      z″ = z

    open Z using (ź; z″) --partial opening

    y₂ = suc ź
    -- y₂́ = suc z -- not accessible

  x₂ = suc Y.y₂

-- Partial opening (2)
module X⁶ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      ź = z
      z″ = z

    open Z hiding (z) -- partial opening

    y₂ = suc ź
    -- y₂́ = suc z -- not accessible

  x₂ = suc Y.y₂


-- Renaming
module X⁷ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      ź = z
      z″ = z

    open Z renaming (z to v; z″ to v″) -- renamings

    y₂ = suc v
    -- y₂″ = suc z -- not accessible
    y₂́ = suc ź -- accessible

  x₂ = suc Y.y₂



