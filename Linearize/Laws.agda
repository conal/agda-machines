{-# OPTIONS --safe --without-K #-}

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws

module Linearize.Laws {ℓₘ}{objₘ : Set ℓₘ} ⦃ _ : Products objₘ ⦄
             (_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             q ⦃ equivₘ : Equivalent q _⇨ₘ_ ⦄
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄
             ⦃ _ : Monoidal _⇨ₘ_ ⦄ ⦃ _ : LawfulMonoidal _⇨ₘ_ q ⦄
             ⦃ _ : Braided  _⇨ᵣ_ ⦄
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             ⦃ _ : ProductsH _⇨ᵣ_ _⇨ₘ_ q ⦄
             ⦃ monoidalHᵣ : MonoidalH _⇨ᵣ_ _⇨ₘ_ q ⦄
  where

open import Level using (0ℓ)

open import Categorical.MakeLawful

open import Linearize.Raw          _⇨ₘ_ _⇨ₚ_ _⇨ᵣ_ q
open import Linearize.Homomorphism _⇨ₘ_ _⇨ₚ_ _⇨ᵣ_ q

module routing-laws where

  instance

    equivalent : Equivalent q _⇨_
    equivalent = H-equiv homomorphism

    lawful-category : LawfulCategory _⇨_ q
    lawful-category = LawfulCategoryᶠ _⇨ₘ_

    -- lawful-monoidal : LawfulMonoidal _⇨_ 0ℓ
    -- lawful-monoidal = LawfulMonoidalᶠ monoidalH
