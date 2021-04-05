-- Symbolic logic primitives

module Symbolic.Prim where

open import Category
open import Ty

private variable A B : Ty

infix 1 _⇨_
data _⇨_ : Ty → Ty → Set where
  `∧ `∨ `xor : Bool × Bool ⇨ Bool
  `not : Bool ⇨ Bool
  `const : ⟦ A ⟧ → ⊤ ⇨ A

instance

  meaningful : Meaningful {μ = A ty.⇨ B} (A ⇨ B)
  meaningful = record
    { ⟦_⟧ = λ { `∧         → ty.mk ∧
              ; `∨         → ty.mk ∨
              ; `xor       → ty.mk xor
              ; `not       → ty.mk not
              ; (`const a) → ty.mk (const a) } }

  p-show : Show (A ⇨ B)
  p-show = record { show = λ { `∧ → "∧"
                             ; `∨ → "∨"
                             ; `xor → "⊕"
                             ; `not → "not"
                             ; (`const x) → showTy x
                             }
                  }

  constants : Constant _⇨_
  constants = record { const = `const }

  logic : Logic _⇨_
  logic = record { ∧ = `∧ ; ∨ = `∨ ; xor = `xor ; not = `not }
