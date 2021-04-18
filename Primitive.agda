{-# OPTIONS --safe --without-K #-}
-- Symbolic logic primitives

module Primitive where

open import Category
open import Ty

private variable A B : Ty

infix 1 _⇨_
data _⇨_ : Ty → Ty → Set where
  `false `true : ⊤ ⇨ Bool
  `not : Bool ⇨ Bool
  `∧ `∨ `xor : Bool × Bool ⇨ Bool
  `cond : Bool × (A × A) ⇨ A

instance

  meaningful : Meaningful {μ = A ty.⇨ B} (A ⇨ B)
  meaningful = record
    { ⟦_⟧ = λ { `false → ty.mk false
              ; `true  → ty.mk true
              ; `not   → ty.mk not
              ; `∧     → ty.mk ∧
              ; `∨     → ty.mk ∨
              ; `xor   → ty.mk xor
              ; `cond  → ty.mk cond
              } }

  p-show : Show (A ⇨ B)
  p-show = record { show = λ { `false → "false"
                             ; `true  → "true"
                             ; `not   → "not"
                             ; `∧     → "∧"
                             ; `∨     → "∨"
                             ; `xor   → "⊕"
                             ; `cond  → "cond"
                             }
                  }

  logic : Logic _⇨_
  logic = record { false = `false ; true = `true
                 ; not = `not ; ∧ = `∧ ; ∨ = `∨ ; xor = `xor ; cond = `cond}

  -- ⟦⟧-Hₒ : Homomorphismₒ Ty Ty
  -- ⟦⟧-Hₒ = id-Hₒ

  -- TODO: Why is ⟦⟧-Hₒ needed in Symbolic but not here, considering
  -- that id-homomorphismₒ is visible to both?

  ⟦⟧-H : Homomorphism _⇨_ ty._⇨_
  ⟦⟧-H = record { Fₘ = ⟦_⟧ }

  open import Relation.Binary.PropositionalEquality

  open import Level using (0ℓ)

  logicH : LogicH _⇨_ ty._⇨_ 0ℓ
  logicH = record
             { F-Bool  = refl
             ; F-false = λ _ → refl
             ; F-true  = λ _ → refl
             ; F-not   = λ _ → refl
             ; F-∧     = λ _ → refl
             ; F-∨     = λ _ → refl
             ; F-xor   = λ _ → refl
             }
