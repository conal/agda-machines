{-# OPTIONS --safe --without-K #-}
-- Symbolic logic primitives with mapping to another category

open import Level
open import Categorical.Raw

module Primitive
    {o ℓ} {obj : Set o} (_↠_ : obj → obj → Set ℓ)
    ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _↠_ ⦄
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

open import Categorical.Homomorphism
open import Categorical.Laws

-- TODO: Replace with single import
open import Typed.Raw          _↠_ renaming (_⇨_ to _⇨ₜ_)
open import Typed.Homomorphism _↠_ q
open import Typed.Laws         _↠_ q

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

  productsH : ⦃ _ : Category _↠_ ⦄
              ⦃ lcat : LawfulCategory _↠_ q ⦄
            → ProductsH _⇨_ _⇨ₜ_ q
  productsH = id-productsH

  booleanH : ⦃ _ : Category _↠_ ⦄
           → BooleanH _⇨_ _⇨ₜ_
  booleanH = id-booleanH

  -- Help type inference along
  open Equiv {q = q}{_⇨_ = _↠_} using () renaming (sym to sym↠; trans to trans↠)

  logicH : ⦃ _ : Monoidal _↠_ ⦄ ⦃ lmon : LawfulMonoidal _↠_ q ⦄
         → LogicH _⇨_ _⇨ₜ_ q
  logicH ⦃ lmon = lmon ⦄ =
    let -- Help type inference along
        open LawfulCategory (LawfulMonoidal.lawful-cat lmon) using ()
               renaming (identityˡ to identityˡ↠; identityʳ to identityʳ↠) in
      record
        { F-false = trans↠ identityʳ↠ (sym↠ identityˡ↠)
        ; F-true  = trans↠ identityʳ↠ (sym↠ identityˡ↠)
        ; F-not   = trans↠ identityʳ↠ (sym↠ identityˡ↠)
        ; F-∧     = trans↠ ∘id⊗       (sym↠ identityˡ↠)
        ; F-∨     = trans↠ ∘id⊗       (sym↠ identityˡ↠)
        ; F-xor   = trans↠ ∘id⊗       (sym↠ identityˡ↠)
        }

  -- TODO: Generalize to id-LogicH. See start in Categorical.Homomorphism
