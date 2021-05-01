{-# OPTIONS --safe --without-K #-}

open import Level using (Level)
open import Categorical.Raw

module Typed.Homomorphism
    {o ℓ} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
    (_↠_ : obj → obj → Set ℓ)
    (q : Level) ⦃ _ : Equivalent q _↠_ ⦄
  where

import Relation.Binary.PropositionalEquality as ≡

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws

open import Miscellany
open import Categorical.Instances.Function
open import Typed.Raw _↠_

open Equiv {q = q}{_⇨_ = _↠_} using () renaming (sym to sym↠; trans to trans↠)

module typed-hom where

  private
    -- Category-specialized
    refl′ : {a b : obj} {f : a ↠ b} → f ≈ f
    refl′ = refl

  instance

    Hₒ : Homomorphismₒ Ty obj
    Hₒ = record { Fₒ = ⟦_⟧ }

    H : Homomorphism _⇨_ _↠_
    H = record { Fₘ = _⇨_.f }

    equivalent : Equivalent q _⇨_
    equivalent = H-equiv H

    categoryH : ⦃ _ : Category _↠_ ⦄ → CategoryH _⇨_ _↠_ q
    categoryH = record { F-id = refl′ ; F-∘ = λ f g → refl′ }

    productsH : ⦃ _ : Category _↠_ ⦄ ⦃ _ : LawfulCategory _↠_ q ⦄
              → ProductsH _⇨_ _↠_ q
    productsH = record { ε     = id
                       ; μ     = id
                       ; ε⁻¹   = id
                       ; μ⁻¹   = id
                       ; ε∘ε⁻¹ = identityˡ
                       ; ε⁻¹∘ε = identityˡ
                       ; μ∘μ⁻¹ = identityˡ
                       ; μ⁻¹∘μ = identityˡ
                       }

    monoidalH : ⦃ _ : Monoidal _↠_ ⦄ ⦃ _ : LawfulMonoidal _↠_ q ⦄
              → MonoidalH _⇨_ _↠_ q
    monoidalH = record
      { F-unitorᵉˡ = ∘id⊗
      ; F-unitorⁱˡ = sym↠ id⊗∘
      ; F-unitorᵉʳ = ∘id⊗
      ; F-unitorⁱʳ = sym↠ id⊗∘
      ; F-assocˡ   = trans↠ ∘id⊗ (sym↠ id⊗∘)
      ; F-assocʳ   = trans↠ ∘id⊗ (sym↠ id⊗∘)
      ; F-!        = sym↠ identityˡ
      ; F-⊗ = λ f g → trans↠ identityʳ (sym↠ identityˡ)
      }

    braidedH : ⦃ _ : Braided _↠_ ⦄ ⦃ _ : LawfulMonoidal _↠_ q ⦄
             → BraidedH _⇨_ _↠_ q
    braidedH = record {
      F-swap = trans↠ identityʳ (sym↠ identityˡ) }

    cartesianH : ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : LawfulMonoidal _↠_ q ⦄
             → CartesianH _⇨_ _↠_ q
    cartesianH = record
      { F-exl = identityʳ
      ; F-exr = identityʳ
      ; F-dup = sym↠ identityˡ
      }

    booleanH : ⦃ Category _↠_ ⦄ → BooleanH _⇨_ _↠_
    booleanH = record { β = id }

    logicH : ⦃ _ : Monoidal _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
             ⦃ _ : LawfulMonoidal _↠_ q ⦄
           → LogicH _⇨_ _↠_ q
    logicH = record
       { F-false = trans↠ identityʳ (sym↠ identityˡ)
       ; F-true  = trans↠ identityʳ (sym↠ identityˡ)
       ; F-not   = trans↠ identityʳ (sym↠ identityˡ)
       ; F-∧     = trans↠ ∘id⊗      (sym↠ identityˡ)
       ; F-∨     = trans↠ ∘id⊗      (sym↠ identityˡ)
       ; F-xor   = trans↠ ∘id⊗      (sym↠ identityˡ)
       }

-- We could almost say productsH = id-productsH, etc, but we'd have to
-- generalize id-productsH to take equality proofs. Ditto for the other
-- homomorphisms.
