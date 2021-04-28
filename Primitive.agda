{-# OPTIONS --safe --without-K #-}
-- Symbolic logic primitives

module Primitive where

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Instances.Function.Raw

-- TODO: Replace with single import
open import Ty.Raw as ty hiding (_⇨_)
open import Ty.Homomorphism
open import Ty.Laws

private variable A B : Ty

infix 0 _⇨_
data _⇨_ : Ty → Ty → Set where
  `false `true : ⊤ ⇨ Bool
  `not : Bool ⇨ Bool
  `∧ `∨ `xor : Bool × Bool ⇨ Bool
  `cond : Bool × (A × A) ⇨ A

instance

  Hₒ : Homomorphismₒ Ty Ty
  Hₒ = id-Hₒ

  H : Homomorphism _⇨_ ty._⇨_
  H = record { Fₘ = λ { `false → mk false
                      ; `true  → mk true
                      ; `not   → mk not
                      ; `∧     → mk ∧
                      ; `∨     → mk ∨
                      ; `xor   → mk xor
                      ; `cond  → mk cond
                      }
             }

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

  -- open import Relation.Binary.PropositionalEquality

  open import Level using (0ℓ)

  productsH : ProductsH _⇨_ ty._⇨_ 0ℓ
  productsH = id-productsH

  booleanH : BooleanH _⇨_ ty._⇨_
  booleanH = id-booleanH

  logicH : LogicH _⇨_ ty._⇨_ 0ℓ
  logicH = record
             { F-false = refl
             ; F-true  = refl
             ; F-not   = refl
             ; F-∧     = refl
             ; F-∨     = refl
             ; F-xor   = refl
             }
