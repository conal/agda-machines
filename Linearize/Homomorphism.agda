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

private variable a b c d : obj

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

{-

⟦first⟧ : {b : obj} (f : a ⇨ c) → ⟦ firstₖ {b = b} f ⟧ₖ ≈ firstᴴ ⟦ f ⟧ₖ
⟦first⟧ ⌞ r ⌟ = F-first r
⟦first⟧ (f ∘·first p ∘ r) =
  begin
    ⟦ firstₖ (f ∘·first p ∘ r) ⟧ₖ
  ≡⟨⟩
    ⟦ (firstₖ f ∘ ⌞ assocˡ ⌟) ∘·first p ∘ (assocʳ ∘ first r) ⟧ₖ
  ≡⟨⟩
    ⟦ firstₖ f ∘ ⌞ assocˡ ⌟ ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ assocʳ ∘ first r ⟧ᵣ
  ≈⟨ ∘-resp-≈ {_⇨′_ = _⇨ₘ_} (firstₖ f ⟦∘⟧ ⌞ assocˡ ⌟)
        (∘-resp-≈ʳ {_⇨′_ = _⇨ₘ_} (F-∘ assocʳ (first r))) ⟩
    (⟦ firstₖ f ⟧ₖ ∘ ⟦ assocˡ ⟧ᵣ) ∘ firstᴴ ⟦ p ⟧ₚ ∘ (⟦ assocʳ ⟧ᵣ ∘ ⟦ first r ⟧ᵣ)
  ≈˘⟨ ∘-resp-≈ʳ {_⇨′_ = _⇨ₘ_} (assoc {_⇨′_ = _⇨ₘ_}) ⟩
    (⟦ firstₖ f ⟧ₖ ∘ ⟦ assocˡ ⟧ᵣ) ∘ (firstᴴ ⟦ p ⟧ₚ ∘ ⟦ assocʳ ⟧ᵣ) ∘ ⟦ first r ⟧ᵣ
  ≈⟨ assoc {_⇨′_ = _⇨ₘ_} ⟩
    ⟦ firstₖ f ⟧ₖ ∘ ⟦ assocˡ ⟧ᵣ ∘ (firstᴴ ⟦ p ⟧ₚ ∘ ⟦ assocʳ ⟧ᵣ) ∘ ⟦ first r ⟧ᵣ
  ≈˘⟨ ∘-resp-≈ʳ {_⇨′_ = _⇨ₘ_} (assoc {_⇨′_ = _⇨ₘ_}) ⟩
    ⟦ firstₖ f ⟧ₖ ∘ (⟦ assocˡ ⟧ᵣ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ assocʳ ⟧ᵣ) ∘ ⟦ first r ⟧ᵣ
  ≈⟨ ∘-resp-≈ʳ {_⇨′_ = _⇨ₘ_} (∘-resp-≈ {_⇨′_ = _⇨ₘ_} (∘-resp-≈ {_⇨′_ = _⇨ₘ_} F-assocˡ (∘-resp-≈ʳ {_⇨′_ = _⇨ₘ_} F-assocʳ)) (F-first r)) ⟩
    ⟦ firstₖ f ⟧ₖ ∘ (assocᴴˡ ∘ firstᴴ ⟦ p ⟧ₚ ∘ assocᴴʳ) ∘ firstᴴ ⟦ r ⟧ᵣ
  ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ {!!}) ⟩
    firstᴴ ⟦ f ⟧ₖ ∘ firstᴴ (firstᴴ ⟦ p ⟧ₚ) ∘ firstᴴ ⟦ r ⟧ᵣ
  ≈⟨ ∘-resp-≈ʳ {_⇨′_ = _⇨ₘ_} first∘firstᴴ ⟩
    firstᴴ ⟦ f ⟧ₖ ∘ firstᴴ (firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ)
  ≈⟨ first∘firstᴴ ⟩
    firstᴴ (⟦ f ⟧ₖ ∘ firstᴴ ⟦ p ⟧ₚ ∘ ⟦ r ⟧ᵣ)
  ≡⟨⟩
    firstᴴ ⟦ f ∘·first p ∘ r ⟧ₖ
  ∎

⟦second⟧ : (g : b ⇨ d) → ⟦ secondₖ {a = a} g ⟧ₖ ≈ secondᴴ ⟦ g ⟧ₖ
⟦second⟧ g = {!!}

infixr 7 _⟦⊗⟧_
_⟦⊗⟧_ : ∀ (f : a ⇨ c) (g : b ⇨ d) → ⟦ f ⊗ g ⟧ₖ ≈ ⟦ f ⟧ₖ ⊗ᴴ ⟦ g ⟧ₖ

f ⟦⊗⟧ g =
  begin
    ⟦ f ⊗ g ⟧ₖ
  ≡⟨⟩
    ⟦ secondₖ g ∘ firstₖ f ⟧ₖ
  ≈⟨ secondₖ g ⟦∘⟧ firstₖ f ⟩
    ⟦ secondₖ g ⟧ₖ ∘ ⟦ firstₖ f ⟧ₖ
    ≈⟨ ∘-resp-≈ {_⇨′_ = _⇨ₘ_} (⟦second⟧ g) (⟦first⟧ f) ⟩
    secondᴴ ⟦ g ⟧ₖ ∘ firstᴴ ⟦ f ⟧ₖ
  ≈⟨ second∘firstᴴ ⟩
    ⟦ f ⟧ₖ ⊗ᴴ ⟦ g ⟧ₖ
  ∎

-}

instance

  homomorphism : Homomorphism _⇨_ _⇨ₘ_
  homomorphism = record { Fₘ = ⟦_⟧ₖ }

  categoryH : CategoryH _⇨_ _⇨ₘ_ q
  categoryH = record { F-id = F-id {_⇨₁_ = _⇨ᵣ_} ; F-∘ = _⟦∘⟧_ }

  -- -- Most properties transfer from monoidalHᵣ.
  -- monoidalH : MonoidalH _⇨_ _⇨ₘ_ q
  -- monoidalH = record
  --               { F-!        = F-!
  --               ; F-⊗        = _⟦⊗⟧_
  --               ; F-unitorᵉˡ = F-unitorᵉˡ
  --               ; F-unitorⁱˡ = F-unitorⁱˡ
  --               ; F-unitorᵉʳ = F-unitorᵉʳ
  --               ; F-unitorⁱʳ = F-unitorⁱʳ
  --               ; F-assocˡ   = F-assocˡ
  --               ; F-assocʳ   = F-assocʳ
  --               }
