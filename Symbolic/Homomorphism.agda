{-# OPTIONS --safe --without-K #-}

-- Symbolic category

module Symbolic.Homomorphism where

open import Level using (Level; 0ℓ)

open import Miscellany using (Function)
open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Instances.Function.Raw
open import Categorical.Instances.Function.Laws

private
  _↠_ : Set → Set → Set
  _↠_ = Function {0ℓ}

  q : Level
  q = 0ℓ

open import Ty
open import Typed _↠_ q renaming (_⇨_ to _⇨ₜ_)

open import Routing as r using (swizzle-id)
import Primitive _↠_ q as p

open import Symbolic.Raw

private variable a b c d : Ty

private
  -- Category-specialized
  refl′ : ∀ {o}{a b : Set o} {f : a → b} → f ≈ f
  refl′ = refl

instance

  Hₒ : Homomorphismₒ Ty Ty
  Hₒ = id-Hₒ

  H : Homomorphism _⇨_ _⇨ₜ_ ⦃ Hₒ = Hₒ ⦄
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
    { F-id = λ {a} _ → swizzle-id a
    ; F-∘  = λ g f → refl′   -- direct from _∘_ definition
    }

  productsH : ProductsH _⇨_ _⇨ₜ_ 0ℓ
  productsH = id-productsH

  monoidalH : MonoidalH _⇨_ _⇨ₜ_ 0ℓ
  monoidalH = record
                { F-unitorᵉˡ = λ {a}     _ → swizzle-id a
                ; F-unitorⁱˡ = λ {a}     _ → swizzle-id (⊤ × a)
                ; F-unitorᵉʳ = λ {a}     _ → swizzle-id a
                ; F-unitorⁱʳ = λ {a}     _ → swizzle-id (a × ⊤)
                ; F-assocˡ   = λ {a b c} _ → swizzle-id ((a × b) × c)
                ; F-assocʳ   = λ {a b c} _ → swizzle-id (a × (b × c))
                ; F-!        = λ         _ → swizzle-id ⊤
                ; F-⊗        = λ f g → refl′
                }

  braidedH : BraidedH _⇨_ _⇨ₜ_ 0ℓ
  braidedH = record { F-swap = λ {a b} _ → swizzle-id (b × a) }

  cartesianH : CartesianH _⇨_ _⇨ₜ_ 0ℓ
  cartesianH = record
    { F-exl = λ {a b} _ → swizzle-id a
    ; F-exr = λ {a b} _ → swizzle-id b
    ; F-dup = λ {a}   _ → swizzle-id (a × a)
    }

  -- TODO: Use monoidalH, braidedH, and cartesianH from Routing.Homomorphism.
