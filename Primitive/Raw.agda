{-# OPTIONS --safe --without-K #-}
-- Symbolic logic primitives with mapping to another category

open import Level
open import Categorical.Raw

module Primitive.Raw
    {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _↠_ ⦄
  where

open import Categorical.Homomorphism
open import Categorical.Laws

open import Primitive.Type public

open import Typed.Raw _↠_ renaming (_⇨_ to _⇨ₜ_)

private variable a b : Ty

module primitive-instances where

  instance

    Hₒ : Homomorphismₒ Ty Ty
    Hₒ = id-Hₒ

    H : Homomorphism _⇨_ _⇨ₜ_
    H = record { Fₘ = λ { `false → mk false
                        ; `true  → mk true
                        ; `not   → mk not
                        ; `∧     → mk ∧
                        ; `∨     → mk ∨
                        ; `xor   → mk xor
                        ; `cond  → mk cond
                        }
               }

    p-show : Show (a ⇨ b)
    p-show = record { show = showₚ }

    -- p-show = record { show = λ { `false → "false"
    --                            ; `true  → "true"
    --                            ; `not   → "not"
    --                            ; `∧     → "∧"
    --                            ; `∨     → "∨"
    --                            ; `xor   → "⊕"
    --                            ; `cond  → "cond"
    --                            }
    --                 }

    logic : Logic _⇨_
    logic = record { false = `false ; true = `true
                   ; not = `not ; ∧ = `∧ ; ∨ = `∨ ; xor = `xor ; cond = `cond}
