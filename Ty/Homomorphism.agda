{-# OPTIONS --safe --without-K #-}

module Ty.Homomorphism where

open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as ≡

open import Categorical.Raw
open import Categorical.Homomorphism

open import Miscellany
open import Categorical.Instances.Function
open import Ty.Raw

module ty-hom where

  instance

    H : Homomorphism _⇨_ (Function {0ℓ})
    H = record { Fₘ = _⇨_.⟦_⟧ }

    equivalent : Equivalent 0ℓ _⇨_
    equivalent = H-equiv H

    categoryH : CategoryH _⇨_ Function 0ℓ
    categoryH = record { F-id = λ _ → ≡.refl ; F-∘ = λ f g _ → ≡.refl }

    productsH : ProductsH _⇨_ Function 0ℓ
    productsH = record
                  { ε     = id
                  ; μ     = id
                  ; ε⁻¹   = id
                  ; μ⁻¹   = id
                  ; ε∘ε⁻¹ = λ _ → ≡.refl
                  ; ε⁻¹∘ε = λ _ → ≡.refl
                  ; μ∘μ⁻¹ = λ _ → ≡.refl
                  ; μ⁻¹∘μ = λ _ → ≡.refl
                  }

    monoidalH : MonoidalH _⇨_ Function 0ℓ
    monoidalH = record
                  { F-unitorᵉˡ = λ _ → ≡.refl
                  ; F-unitorⁱˡ = λ _ → ≡.refl
                  ; F-unitorᵉʳ = λ _ → ≡.refl
                  ; F-unitorⁱʳ = λ _ → ≡.refl
                  ; F-assocˡ   = λ _ → ≡.refl
                  ; F-assocʳ   = λ _ → ≡.refl
                  ; F-!        = λ _ → ≡.refl
                  ; F-⊗        = λ f g _ → ≡.refl
                  }

    braidedH : BraidedH _⇨_ Function 0ℓ
    braidedH = record { F-swap = λ _ → ≡.refl }

    cartesianH : CartesianH _⇨_ Function 0ℓ
    cartesianH = record
      { F-exl = λ _ → ≡.refl ; F-exr = λ _ → ≡.refl ; F-dup = λ _ → ≡.refl }

    booleanH : BooleanH _⇨_ Function
    booleanH = record { β = id }

    logicH : LogicH _⇨_ Function 0ℓ
    logicH = record
       { F-false = λ _ → ≡.refl
       ; F-true  = λ _ → ≡.refl
       ; F-not   = λ _ → ≡.refl
       ; F-∧     = λ _ → ≡.refl
       ; F-∨     = λ _ → ≡.refl
       ; F-xor   = λ _ → ≡.refl
       }
