{-# OPTIONS --safe --without-K #-}
-- Symbolic logic primitives

module Primitive where

open import Category
open import Ty

private variable A B : Ty

infix 1 _⇨_
data _⇨_ : Ty → Ty → Set where
  `∧ `∨ `xor : Bool × Bool ⇨ Bool
  `not : Bool ⇨ Bool
  `false `true : ⊤ ⇨ Bool

instance

  meaningful : Meaningful {μ = A ty.⇨ B} (A ⇨ B)
  meaningful = record
    { ⟦_⟧ = λ { `∧     → ty.mk ∧
              ; `∨     → ty.mk ∨
              ; `xor   → ty.mk xor
              ; `not   → ty.mk not
              ; `false → ty.mk false
              ; `true  → ty.mk true
              } }

  p-show : Show (A ⇨ B)
  p-show = record { show = λ { `∧     → "∧"
                             ; `∨     → "∨"
                             ; `xor   → "⊕"
                             ; `not   → "not"
                             ; `false → "false"
                             ; `true  → "true"
                             }
                  }

  logic : Logic _⇨_
  logic = record { ∧ = `∧ ; ∨ = `∨ ; xor = `xor ; not = `not
                 ; false = `false ; true = `true }
