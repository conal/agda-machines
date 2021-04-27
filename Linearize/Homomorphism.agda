{-# OPTIONS --safe --without-K #-}

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws

module Linearize.Homomorphism {ℓₘ}{objₘ : Set ℓₘ} ⦃ _ : Products objₘ ⦄
             (_⇨ₘ_ : objₘ → objₘ → Set ℓₘ) (let infix 0 _⇨ₘ_; _⇨ₘ_ = _⇨ₘ_)
             {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄
             (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
             (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
             q ⦃ equivₘ : Equivalent q _⇨ₘ_ ⦄
             ⦃ Hₒ : Homomorphismₒ obj objₘ ⦄
             ⦃ _ : Monoidal _⇨ₘ_ ⦄ ⦃ _ : LawfulCategory _⇨ₘ_ q ⦄
             ⦃ _ : Braided  _⇨ᵣ_ ⦄
             ⦃ Hₚ : Homomorphism _⇨ₚ_ _⇨ₘ_ ⦄
             ⦃ Hᵣ : Homomorphism _⇨ᵣ_ _⇨ₘ_ ⦄
             ⦃ _ : ProductsH _⇨ᵣ_ _⇨ₘ_ q ⦄
             ⦃ monoidalHᵣ : MonoidalH _⇨ᵣ_ _⇨ₘ_ q ⦄
  where


open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws

open import Linearize.Raw _⇨ₘ_ _⇨ₚ_ _⇨ᵣ_ q

private variable a b c d z : obj

open Homomorphismₒ Hₒ -- using () renaming (Fₒ to ⟦_⟧ₒ)
open MonoidalH monoidalHᵣ

open Homomorphism Hₚ using () renaming (Fₘ to ⟦_⟧ₚ)
open Homomorphism Hᵣ using () renaming (Fₘ to ⟦_⟧ᵣ)

open ≈-Reasoning

infixr 9 _⟦∘⟧_
_⟦∘⟧_ : ∀ (g : b ⇨ c) (f : a ⇨ b) → ⟦ g ∘ f ⟧ₖ ≈ ⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ

g ⟦∘⟧ (f ∘·first p ∘ r) =
  begin
    ⟦ g ∘ (f ∘·first p ∘ r) ⟧ₖ
  ≡⟨⟩
    ⟦ (g ∘ f) ∘·first p ∘ r ⟧ₖ
  ≡⟨⟩
    ⟦ g ∘ f ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r ⟧ᵣ
  ≈⟨ ∘-resp-≈ˡ (g ⟦∘⟧ f) ⟩
    (⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ) ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r ⟧ᵣ
  ≈⟨ assoc ⟩
    ⟦ g ⟧ₖ ∘ ⟦ f ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r ⟧ᵣ
  ≡⟨⟩
    ⟦ g ⟧ₖ ∘ ⟦ f ∘·first p ∘ r ⟧ₖ
  ∎

(g ∘·first p ∘ r₂) ⟦∘⟧ ⌞ r₁ ⌟ =
  begin
    ⟦ (g ∘·first p ∘ r₂) ∘ ⌞ r₁ ⌟ ⟧ₖ
  ≡⟨⟩
    ⟦ g ∘·first p ∘ (r₂ ∘ r₁) ⟧ₖ
  ≡⟨⟩
    ⟦ g ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r₂ ∘ r₁ ⟧ᵣ
  ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ʳ (F-∘ r₂ r₁)))) ⟩
    ⟦ g ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r₂ ⟧ᵣ ∘ ⟦ r₁ ⟧ᵣ
  ≈˘⟨ assoc⁵ ⟩
    (⟦ g ⟧ₖ ∘ μ ∘ first ⟦ p ⟧ₚ ∘ μ⁻¹ ∘ ⟦ r₂ ⟧ᵣ) ∘ ⟦ r₁ ⟧ᵣ
  ≡⟨⟩
    ⟦ g ∘·first p ∘ r₂ ⟧ₖ ∘ ⟦ ⌞ r₁ ⌟ ⟧ₖ
  ∎

⌞ r₂ ⌟ ⟦∘⟧ ⌞ r₁ ⌟ = F-∘ r₂ r₁

instance

  homomorphism : Homomorphism _⇨_ _⇨ₘ_
  homomorphism = record { Fₘ = ⟦_⟧ₖ }

  -- equivalent : Equivalent q _⇨_
  -- equivalent = H-equiv homomorphism

  categoryH : CategoryH _⇨_ _⇨ₘ_ q
  categoryH = record { F-id = F-id ; F-∘ = _⟦∘⟧_ }  -- F-id from monoidalHᵣ

  -- lawful-category : LawfulCategory _⇨_ q ⦃ equiv = equivalent ⦄
  -- lawful-category = LawfulCategoryᶠ categoryH

