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
  p-show = record { show = λ { `false → "false"
                             ; `true  → "true"
                             ; `not   → "not"
                             ; `∧     → "∧"
                             ; `∨     → "∨"
                             ; `xor   → "⊕"
                             }
                  }

  logic : Logic _⇨_
  logic = record { false = `false ; true = `true
                 ; not = `not ; ∧ = `∧ ; ∨ = `∨ ; xor = `xor }

  -- ⟦⟧-homomorphismₒ : Homomorphismₒ Ty Ty
  -- ⟦⟧-homomorphismₒ = id-homomorphismₒ

  -- TODO: Why is ⟦⟧-homomorphismₒ needed in Symbolic but not here, considering
  -- that id-homomorphismₒ is visible to both?

  ⟦⟧-homomorphism : Homomorphism _⇨_ ty._⇨_
  ⟦⟧-homomorphism = record { Fₘ = ⟦_⟧ }

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
