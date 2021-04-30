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

  private
    -- Category-specialized
    refl′ : {a b : Set} {f : a → b} → f ≈ f
    refl′ = refl

  instance

    H : Homomorphism _⇨_ (Function {0ℓ})
    H = record { Fₘ = _⇨_.⟦_⟧ }

    equivalent : Equivalent 0ℓ _⇨_
    equivalent = H-equiv H

    categoryH : CategoryH _⇨_ Function 0ℓ
    categoryH = record { F-id = refl′ ; F-∘ = λ f g → refl′ }

    productsH : ProductsH _⇨_ Function 0ℓ
    productsH = record
                  { ε     = id
                  ; μ     = id
                  ; ε⁻¹   = id
                  ; μ⁻¹   = id
                  ; ε∘ε⁻¹ = refl′
                  ; ε⁻¹∘ε = refl′
                  ; μ∘μ⁻¹ = refl′
                  ; μ⁻¹∘μ = refl′
                  }

    monoidalH : MonoidalH _⇨_ Function 0ℓ
    monoidalH = record
                  { F-unitorᵉˡ = refl′
                  ; F-unitorⁱˡ = refl′
                  ; F-unitorᵉʳ = refl′
                  ; F-unitorⁱʳ = refl′
                  ; F-assocˡ   = refl′
                  ; F-assocʳ   = refl′
                  ; F-!        = refl′
                  ; F-⊗        = λ f g → refl′
                  }

    braidedH : BraidedH _⇨_ Function 0ℓ
    braidedH = record { F-swap = refl′ }

    cartesianH : CartesianH _⇨_ Function 0ℓ
    cartesianH = record
      { F-exl = refl′ ; F-exr = refl′ ; F-dup = refl′ }

    booleanH : BooleanH _⇨_ Function
    booleanH = record { β = id }

    logicH : LogicH _⇨_ Function 0ℓ
    logicH = record
       { F-false = refl′
       ; F-true  = refl′
       ; F-not   = refl′
       ; F-∧     = refl′
       ; F-∨     = refl′
       ; F-xor   = refl′
       }
