-- Symbolic logic primitives
{-# OPTIONS --safe --without-K #-}

module Primitive.Type where

open import Ty

infix 0 _⇨_
data _⇨_ : Ty → Ty → Set where
  `false `true : `⊤ ⇨ `Bool
  `not : `Bool ⇨ `Bool
  `∧ `∨ `xor : `Bool `× `Bool ⇨ `Bool
  `cond : ∀ {a} → `Bool `× (a `× a) ⇨ a

-- showₚ : ∀ {a b} → (a ⇨ b) → String
-- showₚ `false = "false"
-- showₚ `true  = "true"
-- showₚ `not   = "not"
-- showₚ `∧     = "∧"
-- showₚ `∨     = "∨"
-- showₚ `xor   = "⊕"
-- showₚ `cond  = "cond"

instance

  open import Miscellany
  open import Data.String

  p-show : ∀ {a b} → Show (a ⇨ b)
  p-show = record { show = λ { `false → "false"
                             ; `true  → "true"
                             ; `not   → "not"
                             ; `∧     → "∧"
                             ; `∨     → "∨"
                             ; `xor   → "⊕"
                             ; `cond  → "cond"
                             }
                  }
