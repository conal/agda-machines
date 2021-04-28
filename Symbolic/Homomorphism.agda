{-# OPTIONS --safe --without-K #-}

-- Symbolic category

module Symbolic.Homomorphism where

open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as ≡

open import Categorical.Raw
open import Categorical.Homomorphism
open import Ty renaming (_⇨_ to _⇨ₜ_)
open import Routing as r using (swizzle-id)
import Primitive as p

open import Symbolic.Raw

private variable a b c d : Ty

instance

  Hₒ : Homomorphismₒ Ty Ty
  Hₒ = id-Hₒ

  H : Homomorphism _⇨_ _⇨ₜ_
  H = record { Fₘ = ⟦_⟧′ }
   where
     ⟦_⟧′ : (a ⇨ b) → (a ⇨ₜ b)
     ⟦ `route f ⟧′ = Fₘ f
     ⟦ `prim  p ⟧′ = Fₘ p
     ⟦  g `∘ f  ⟧′ = ⟦ g ⟧′ ∘ ⟦ f ⟧′
     ⟦  f `⊗ g  ⟧′ = ⟦ f ⟧′ ⊗ ⟦ g ⟧′

  equivalent : Equivalent 0ℓ _⇨_
  equivalent = H-equiv H

  categoryH : CategoryH _⇨_ _⇨ₜ_ 0ℓ
  categoryH = record
    { F-id = λ x → swizzle-id
    ; F-∘  = λ g f x → ≡.refl   -- direct from _∘_ definition
    }

  productsH : ProductsH _⇨_ _⇨ₜ_ 0ℓ
  productsH = id-productsH

  monoidalH : MonoidalH _⇨_ _⇨ₜ_ 0ℓ
  monoidalH = record
                   { F-unitorᵉˡ = λ _ → swizzle-id
                   ; F-unitorⁱˡ = λ _ → swizzle-id
                   ; F-unitorᵉʳ = λ _ → swizzle-id
                   ; F-unitorⁱʳ = λ _ → swizzle-id
                   ; F-assocʳ   = λ _ → swizzle-id
                   ; F-assocˡ   = λ _ → swizzle-id
                   ; F-!        = λ _ → ≡.refl
                   ; F-⊗        = λ f g _ → ≡.refl
                   }

  braidedH : BraidedH _⇨_ _⇨ₜ_ 0ℓ
  braidedH = record { F-swap = λ _ → swizzle-id }

  cartesianH : CartesianH _⇨_ _⇨ₜ_ 0ℓ
  cartesianH = record
    { F-exl = λ _ → swizzle-id
    ; F-exr = λ _ → swizzle-id
    ; F-dup = λ _ → swizzle-id
    }
