{-# OPTIONS --safe --without-K #-}

-- Make lawfuls from lawfuls and homomorphisms

module Categorical.MakeLawful where

open import Level using (Level)

open import Categorical.Raw
open import Categorical.Homomorphism
open import Categorical.Laws

open ≈-Reasoning

-- TODO: trim imports

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

LawfulCategoryᶠ : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
                  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
                  {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
                  ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Category _⇨₂_ ⦄
                  ⦃ _ : LawfulCategory _⇨₂_ q ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
                  ⦃ F : CategoryH _⇨₁_ _⇨₂_ q ⦄
                → LawfulCategory _⇨₁_ q ⦃ equiv = H-equiv H ⦄
LawfulCategoryᶠ F = record
  { identityˡ = λ {a b} {f} →
      begin
        Fₘ (id ∘ f)
      ≈⟨ F-∘ id f ⟩
        Fₘ id ∘ Fₘ f
      ≈⟨ ∘-resp-≈ˡ F-id  ⟩
        id ∘ Fₘ f
      ≈⟨ identityˡ ⟩
        Fₘ f
      ∎
  ; identityʳ = λ {a b} {f} →
      begin
        Fₘ (f ∘ id)
      ≈⟨ F-∘ f id ⟩
        Fₘ f ∘ Fₘ id
      ≈⟨ ∘-resp-≈ʳ F-id  ⟩
        Fₘ f ∘ id
      ≈⟨ identityʳ ⟩
        Fₘ f
      ∎
  ; assoc = λ {a b c d} {f g h} →
      begin
        Fₘ ((h ∘ g) ∘ f)
      ≈⟨ F-∘ _ _ ⟩
        Fₘ (h ∘ g) ∘ Fₘ f
      ≈⟨ ∘-resp-≈ˡ (F-∘ _ _) ⟩
        (Fₘ h ∘ Fₘ g) ∘ Fₘ f
      ≈⟨ assoc ⟩
        Fₘ h ∘ (Fₘ g ∘ Fₘ f)
      ≈˘⟨ ∘-resp-≈ʳ (F-∘ _ _) ⟩
        Fₘ h ∘ (Fₘ (g ∘ f))
      ≈˘⟨ F-∘ _ _ ⟩
        Fₘ (h ∘ (g ∘ f))
      ∎
  ; ∘-resp-≈ = λ {a b c}{f g h k} h∼k f∼g →
      begin
        Fₘ (h ∘ f)
      ≈⟨ F-∘ h f ⟩
        Fₘ h ∘ Fₘ f
      ≈⟨ ∘-resp-≈ h∼k f∼g ⟩
        Fₘ k ∘ Fₘ g
      ≈˘⟨ F-∘ k g ⟩
        Fₘ (k ∘ g)
      ∎
  }

{-

module LawfulMonoidalH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Monoidal _⇨₁′_ ⦄
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Monoidal _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
    ⦃ mH : MonoidalH _⇨₁′_ _⇨₂′_ q ⦄
    ⦃ laws : LawfulMonoidal _⇨₂′_ q ⦄
    where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_  -- TODO: move into module params

  open MonoidalH mH

  -- TODO: turn the next two around

  postulate

    F-unitorᵉˡ′ : Fₘ unitorᵉˡ ≈ unitorᵉˡ ∘ first ε⁻¹ ∘ μ⁻¹{⊤}{a}

  -- F-unitorᵉˡ′ =
  --   begin
  --     Fₘ unitorᵉˡ
  --   ≈˘⟨ identityʳ ⟩
  --     Fₘ unitorᵉˡ ∘ id
  --   ≈˘⟨ ∘-resp-≈ʳ μ∘μ⁻¹ ⟩
  --     Fₘ unitorᵉˡ ∘ (μ ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ identityˡ) ⟩
  --     Fₘ unitorᵉˡ ∘ (μ ∘ id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id)) ⟩
  --     Fₘ unitorᵉˡ ∘ (μ ∘ first id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ˡ ε∘ε⁻¹))) ⟩
  --     Fₘ unitorᵉˡ ∘ (μ ∘ first (ε ∘ ε⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ first∘first)) ⟩
  --     Fₘ unitorᵉˡ ∘ (μ ∘ (first ε ∘ first ε⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ assoc-middle ⟩
  --     Fₘ unitorᵉˡ ∘ ((μ ∘ first ε) ∘ (first ε⁻¹ ∘ μ⁻¹))
  --   ≈˘⟨ assoc ⟩
  --     (Fₘ unitorᵉˡ ∘ μ ∘ first ε) ∘ first ε⁻¹ ∘ μ⁻¹
  --   ≈⟨ ∘-resp-≈ˡ F-unitorᵉˡ ⟩
  --     unitorᵉˡ ∘ first ε⁻¹ ∘ μ⁻¹
  --   ∎

    F-unitorᵉʳ′ : Fₘ unitorᵉʳ ≈ unitorᵉʳ ∘ second ε⁻¹ ∘ μ⁻¹{a}{⊤}

  -- F-unitorᵉʳ′ =
  --   begin
  --     Fₘ unitorᵉʳ
  --   ≈˘⟨ identityʳ ⟩
  --     Fₘ unitorᵉʳ ∘ id
  --   ≈˘⟨ ∘-resp-≈ʳ μ∘μ⁻¹ ⟩
  --     Fₘ unitorᵉʳ ∘ (μ ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ identityˡ) ⟩
  --     Fₘ unitorᵉʳ ∘ (μ ∘ id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id)) ⟩
  --     Fₘ unitorᵉʳ ∘ (μ ∘ second id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ʳ ε∘ε⁻¹))) ⟩
  --     Fₘ unitorᵉʳ ∘ (μ ∘ second (ε ∘ ε⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ second∘second)) ⟩
  --     Fₘ unitorᵉʳ ∘ (μ ∘ (second ε ∘ second ε⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ assoc-middle ⟩
  --     Fₘ unitorᵉʳ ∘ ((μ ∘ second ε) ∘ (second ε⁻¹ ∘ μ⁻¹))
  --   ≈˘⟨ assoc ⟩
  --     (Fₘ unitorᵉʳ ∘ μ ∘ second ε) ∘ second ε⁻¹ ∘ μ⁻¹
  --   ≈⟨ ∘-resp-≈ˡ F-unitorᵉʳ ⟩
  --     unitorᵉʳ ∘ second ε⁻¹ ∘ μ⁻¹
  --   ∎

    -- Strong variant (using μ⁻¹)
    F-⊗′ : ∀ (f : a ⇨₁ c)(g : b ⇨₁ d) → Fₘ (f ⊗ g) ≈ μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹

  -- F-⊗′ f g =
  --   begin
  --     Fₘ (f ⊗ g)
  --   ≈˘⟨ identityʳ ⟩
  --     Fₘ (f ⊗ g) ∘ id
  --   ≈˘⟨ ∘-resp-≈ʳ μ∘μ⁻¹ ⟩
  --     Fₘ (f ⊗ g) ∘ (μ ∘ μ⁻¹)
  --   ≈˘⟨ assoc ⟩
  --     (Fₘ (f ⊗ g) ∘ μ) ∘ μ⁻¹
  --   ≈⟨ ∘-resp-≈ˡ (F-⊗ f g) ⟩
  --     (μ ∘ (Fₘ f ⊗ Fₘ g)) ∘ μ⁻¹
  --   ≈⟨ assoc ⟩
  --     μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹
  --   ∎

    F-first : (f : a ⇨₁ c) → Fₘ (first f) ∘ μ{a}{b} ≈ μ{c}{b} ∘ first (Fₘ f)

  -- F-first f =
  --   begin
  --     Fₘ (first f) ∘ μ
  --   ≡⟨⟩
  --     Fₘ (f ⊗ id) ∘ μ
  --   ≈⟨ F-⊗ f id ⟩
  --     μ ∘ (Fₘ f ⊗ Fₘ id)
  --   ≈⟨ ∘-resp-≈ʳ (⊗-resp-≈ʳ F-id) ⟩
  --     μ ∘ (Fₘ f ⊗ id)
  --   ≡⟨⟩
  --     μ ∘ first (Fₘ f)
  --   ∎

    F-second : (g : b ⇨₁ d) → Fₘ (second g) ∘ μ{a}{b} ≈ μ{a}{d} ∘ second (Fₘ g)

  -- F-second g = 
  --   begin
  --     Fₘ (second g) ∘ μ
  --   ≡⟨⟩
  --     Fₘ (id ⊗ g) ∘ μ
  --   ≈⟨ F-⊗ id g ⟩
  --     μ ∘ (Fₘ id ⊗ Fₘ g)
  --   ≈⟨ ∘-resp-≈ʳ (⊗-resp-≈ˡ F-id) ⟩
  --     μ ∘ (id ⊗ Fₘ g)
  --   ≡⟨⟩
  --     μ ∘ second (Fₘ g)
  --   ∎

    F-assocˡ′ :
      Fₘ assocˡ ≈ μ{a × b}{c} ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹{a}{b × c}

  -- F-assocˡ′ =
  --   begin
  --     Fₘ assocˡ
  --   ≈˘⟨ identityʳ ⟩
  --     Fₘ assocˡ ∘ id
  --   ≈˘⟨ ∘-resp-≈ʳ μ∘μ⁻¹ ⟩
  --     Fₘ assocˡ ∘ (μ ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ identityˡ) ⟩
  --     Fₘ assocˡ ∘ (μ ∘ id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id)) ⟩
  --     Fₘ assocˡ ∘ (μ ∘ second id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ʳ μ∘μ⁻¹))) ⟩
  --     Fₘ assocˡ ∘ (μ ∘ second (μ ∘ μ⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ second∘second)) ⟩
  --     Fₘ assocˡ ∘ (μ ∘ (second μ ∘ second μ⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ assoc-middle ⟩
  --     Fₘ assocˡ ∘ (μ ∘ second μ) ∘ (second μ⁻¹ ∘ μ⁻¹)
  --   ≈˘⟨ assoc ⟩
  --     (Fₘ assocˡ ∘ μ ∘ second μ) ∘ (second μ⁻¹ ∘ μ⁻¹)
  --   ≈⟨ ∘-resp-≈ˡ F-assocˡ ⟩
  --     (μ ∘ first  μ ∘ assocˡ) ∘ (second μ⁻¹ ∘ μ⁻¹)
  --   ≈⟨ assoc ⟩
  --     μ ∘ (first  μ ∘ assocˡ) ∘ (second μ⁻¹ ∘ μ⁻¹)
  --   ≈⟨ ∘-resp-≈ʳ assoc ⟩
  --     μ ∘ first  μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
  --   ∎

    F-assocʳ′ :
      Fₘ assocʳ ≈ μ{a}{b × c} ∘ second μ ∘ assocʳ ∘ first  μ⁻¹ ∘ μ⁻¹{a × b}{c}

  -- F-assocʳ′ =
  --   begin
  --     Fₘ assocʳ
  --   ≈˘⟨ identityʳ ⟩
  --     Fₘ assocʳ ∘ id
  --   ≈˘⟨ ∘-resp-≈ʳ μ∘μ⁻¹ ⟩
  --     Fₘ assocʳ ∘ (μ ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ identityˡ) ⟩
  --     Fₘ assocʳ ∘ (μ ∘ id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id)) ⟩
  --     Fₘ assocʳ ∘ (μ ∘ first id ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ˡ μ∘μ⁻¹))) ⟩
  --     Fₘ assocʳ ∘ (μ ∘ first (μ ∘ μ⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-resp-≈ˡ first∘first)) ⟩
  --     Fₘ assocʳ ∘ (μ ∘ (first μ ∘ first μ⁻¹) ∘ μ⁻¹)
  --   ≈˘⟨ ∘-resp-≈ʳ assoc-middle ⟩
  --     Fₘ assocʳ ∘ (μ ∘ first μ) ∘ (first μ⁻¹ ∘ μ⁻¹)
  --   ≈˘⟨ assoc ⟩
  --     (Fₘ assocʳ ∘ μ ∘ first μ) ∘ (first μ⁻¹ ∘ μ⁻¹)
  --   ≈⟨ ∘-resp-≈ˡ F-assocʳ ⟩
  --     (μ ∘ second  μ ∘ assocʳ) ∘ (first μ⁻¹ ∘ μ⁻¹)
  --   ≈⟨ assoc ⟩
  --     μ ∘ (second  μ ∘ assocʳ) ∘ (first μ⁻¹ ∘ μ⁻¹)
  --   ≈⟨ ∘-resp-≈ʳ assoc ⟩
  --     μ ∘ second  μ ∘ assocʳ ∘ first μ⁻¹ ∘ μ⁻¹
  --   ∎


LawfulMonoidalᶠ : {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄ {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
                  {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
                  {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
                  ⦃ _ : Monoidal _⇨₁_ ⦄ ⦃ _ : Monoidal _⇨₂_ ⦄
                  ⦃ _ : LawfulMonoidal _⇨₂_ q ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
                  ⦃ pH : ProductsH _⇨₁_ _⇨₂_ q ⦄
                  ⦃ _ : LawfulCategory _⇨₁_ q ⦃ equiv = H-equiv H ⦄ ⦄
                  ⦃ cH : CategoryH _⇨₁_ _⇨₂_ q ⦄
                  ⦃ F : MonoidalH _⇨₁_ _⇨₂_ q ⦄
                → LawfulMonoidal _⇨₁_ q ⦃ equiv = H-equiv H ⦄
LawfulMonoidalᶠ {_⇨₁_ = _⇨₁_} {_⇨₂_ = _⇨₂_} {q = q} ⦃ F = F ⦄ =
  let open MonoidalH F
      open LawfulMonoidalH _⇨₁_ _⇨₂_ q
  in

  record { id⊗id = {!!}

             -- begin
             --   Fₘ (id ⊗ id)
             -- ≈⟨ F-⊗′ id id ⟩
             --   μ ∘ (Fₘ id ⊗ Fₘ id) ∘ μ⁻¹
             -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ F-id F-id)) ⟩
             --   μ ∘ (id ⊗ id) ∘ μ⁻¹
             -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id) ⟩
             --   μ ∘ id ∘ μ⁻¹
             -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
             --   μ ∘ μ⁻¹
             -- ≈⟨ μ∘μ⁻¹ ⟩
             --   id
             -- ≈˘⟨ F-id ⟩
             --   Fₘ id
             -- ∎

         ; ∘⊗ = λ {a₁ b₁ a₂ b₂ a₃ b₃} {f g h k} → {!!}

             -- begin
             --   Fₘ ((h ⊗ k) ∘ (f ⊗ g))
             -- ≈⟨ F-∘ _ _ ⟩
             --   Fₘ (h ⊗ k) ∘ Fₘ (f ⊗ g)
             -- ≈⟨ ∘-resp-≈ (F-⊗′ h k) (F-⊗′ f g) ⟩
             --   (μ ∘ (Fₘ h ⊗ Fₘ k) ∘ μ⁻¹) ∘ (μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹)
             -- ≈˘⟨ ∘-resp-≈ˡ assoc ⟩
             --   ((μ ∘ (Fₘ h ⊗ Fₘ k)) ∘ μ⁻¹) ∘ (μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹)
             -- ≈⟨ assoc-middle ⟩
             --   (μ ∘ (Fₘ h ⊗ Fₘ k)) ∘ (μ⁻¹ ∘ μ) ∘ ((Fₘ f ⊗ Fₘ g) ∘ μ⁻¹)
             -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ μ⁻¹∘μ) ⟩
             --   (μ ∘ (Fₘ h ⊗ Fₘ k)) ∘ id ∘ ((Fₘ f ⊗ Fₘ g) ∘ μ⁻¹)
             -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
             --   (μ ∘ (Fₘ h ⊗ Fₘ k)) ∘ ((Fₘ f ⊗ Fₘ g) ∘ μ⁻¹)
             -- ≈⟨ assoc-middle ⟩
             --   μ ∘ ((Fₘ h ⊗ Fₘ k) ∘ (Fₘ f ⊗ Fₘ g)) ∘ μ⁻¹
             -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ ∘⊗) ⟩
             --   μ ∘ ((Fₘ h ∘ Fₘ f) ⊗ (Fₘ k ∘ Fₘ g)) ∘ μ⁻¹
             -- ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ (F-∘ _ _) (F-∘ _ _))) ⟩
             --   μ ∘ (Fₘ (h ∘ f) ⊗ Fₘ (k ∘ g)) ∘ μ⁻¹
             -- ≈˘⟨ F-⊗′ _ _ ⟩
             --   Fₘ ((h ∘ f) ⊗ (k ∘ g))
             -- ∎

         ; unitorᵉˡ∘unitorⁱˡ = {!!}

            -- begin
            --   Fₘ (unitorᵉˡ ∘ unitorⁱˡ)
            -- ≈⟨ F-∘ _ _ ⟩
            --   Fₘ unitorᵉˡ ∘ Fₘ unitorⁱˡ
            -- ≈⟨ ∘-resp-≈ F-unitorᵉˡ′ F-unitorⁱˡ ⟩
            --   (unitorᵉˡ ∘ first ε⁻¹ ∘ μ⁻¹) ∘ (μ ∘ first ε ∘ unitorⁱˡ)
            -- ≈˘⟨ ∘-resp-≈ˡ assoc ⟩
            --   ((unitorᵉˡ ∘ first ε⁻¹) ∘ μ⁻¹) ∘ (μ ∘ first ε ∘ unitorⁱˡ)
            -- ≈⟨ assoc-middle ⟩
            --   (unitorᵉˡ ∘ first ε⁻¹) ∘ (μ⁻¹ ∘ μ) ∘ (first ε ∘ unitorⁱˡ)
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ μ⁻¹∘μ) ⟩
            --   (unitorᵉˡ ∘ first ε⁻¹) ∘ id ∘ (first ε ∘ unitorⁱˡ)
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   (unitorᵉˡ ∘ first ε⁻¹) ∘ (first ε ∘ unitorⁱˡ)
            -- ≈⟨ assoc-middle ⟩
            --   unitorᵉˡ ∘ (first ε⁻¹ ∘ first ε) ∘ unitorⁱˡ
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ first∘first) ⟩
            --   unitorᵉˡ ∘ first (ε⁻¹ ∘ ε) ∘ unitorⁱˡ
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ˡ ε⁻¹∘ε)) ⟩
            --   unitorᵉˡ ∘ first id ∘ unitorⁱˡ
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id) ⟩
            --   unitorᵉˡ ∘ id ∘ unitorⁱˡ
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   unitorᵉˡ ∘ unitorⁱˡ
            -- ≈⟨ unitorᵉˡ∘unitorⁱˡ ⟩
            --   id
            -- ≈˘⟨ F-id ⟩
            --   Fₘ id
            -- ∎

         ; unitorⁱˡ∘unitorᵉˡ = {!!}

            -- begin
            --   Fₘ (unitorⁱˡ ∘ unitorᵉˡ)
            -- ≈⟨ F-∘ _ _ ⟩
            --   Fₘ unitorⁱˡ ∘ Fₘ unitorᵉˡ
            -- ≈⟨ ∘-resp-≈ F-unitorⁱˡ F-unitorᵉˡ′ ⟩
            --   (μ ∘ first ε ∘ unitorⁱˡ) ∘ (unitorᵉˡ ∘ first ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ˡ (sym≈ assoc) ⟩
            --   ((μ ∘ first ε) ∘ unitorⁱˡ) ∘ (unitorᵉˡ ∘ first ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ assoc-middle ⟩
            --   (μ ∘ first ε) ∘ (unitorⁱˡ ∘ unitorᵉˡ) ∘ (first ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ unitorⁱˡ∘unitorᵉˡ) ⟩
            --   (μ ∘ first ε) ∘ id ∘ (first ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   (μ ∘ first ε) ∘ (first ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ assoc-middle ⟩
            --   μ ∘ (first ε ∘ first ε⁻¹) ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ first∘first) ⟩
            --   μ ∘ first (ε ∘ ε⁻¹) ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ˡ ε∘ε⁻¹)) ⟩
            --   μ ∘ first id ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id) ⟩
            --   μ ∘ id ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   μ ∘ μ⁻¹
            -- ≈⟨ μ∘μ⁻¹ ⟩
            --   id
            -- ≈⟨ sym≈ F-id ⟩
            --   Fₘ id
            -- ∎

         ; unitorᵉʳ∘unitorⁱʳ = {!!}
 
            -- begin
            --   Fₘ (unitorᵉʳ ∘ unitorⁱʳ)
            -- ≈⟨ F-∘ _ _ ⟩
            --   Fₘ unitorᵉʳ ∘ Fₘ unitorⁱʳ
            -- ≈⟨ ∘-resp-≈ F-unitorᵉʳ′ F-unitorⁱʳ ⟩
            --   (unitorᵉʳ ∘ second ε⁻¹ ∘ μ⁻¹) ∘ (μ ∘ second ε ∘ unitorⁱʳ)
            -- ≈˘⟨ ∘-resp-≈ˡ assoc ⟩
            --   ((unitorᵉʳ ∘ second ε⁻¹) ∘ μ⁻¹) ∘ (μ ∘ second ε ∘ unitorⁱʳ)
            -- ≈⟨ assoc-middle ⟩
            --   (unitorᵉʳ ∘ second ε⁻¹) ∘ (μ⁻¹ ∘ μ) ∘ (second ε ∘ unitorⁱʳ)
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ μ⁻¹∘μ) ⟩
            --   (unitorᵉʳ ∘ second ε⁻¹) ∘ id ∘ (second ε ∘ unitorⁱʳ)
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   (unitorᵉʳ ∘ second ε⁻¹) ∘ (second ε ∘ unitorⁱʳ)
            -- ≈⟨ assoc-middle ⟩
            --   unitorᵉʳ ∘ (second ε⁻¹ ∘ second ε) ∘ unitorⁱʳ
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ second∘second) ⟩
            --   unitorᵉʳ ∘ second (ε⁻¹ ∘ ε) ∘ unitorⁱʳ
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ʳ ε⁻¹∘ε)) ⟩
            --   unitorᵉʳ ∘ second id ∘ unitorⁱʳ
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id) ⟩
            --   unitorᵉʳ ∘ id ∘ unitorⁱʳ
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   unitorᵉʳ ∘ unitorⁱʳ
            -- ≈⟨ unitorᵉʳ∘unitorⁱʳ ⟩
            --   id
            -- ≈˘⟨ F-id ⟩
            --   Fₘ id
            -- ∎

         ; unitorⁱʳ∘unitorᵉʳ = {!!}

            -- begin
            --   Fₘ (unitorⁱʳ ∘ unitorᵉʳ)
            -- ≈⟨ F-∘ _ _ ⟩
            --   Fₘ unitorⁱʳ ∘ Fₘ unitorᵉʳ
            -- ≈⟨ ∘-resp-≈ F-unitorⁱʳ F-unitorᵉʳ′ ⟩
            --   (μ ∘ second ε ∘ unitorⁱʳ) ∘ (unitorᵉʳ ∘ second ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ˡ (sym≈ assoc) ⟩
            --   ((μ ∘ second ε) ∘ unitorⁱʳ) ∘ (unitorᵉʳ ∘ second ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ assoc-middle ⟩
            --   (μ ∘ second ε) ∘ (unitorⁱʳ ∘ unitorᵉʳ) ∘ (second ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ unitorⁱʳ∘unitorᵉʳ) ⟩
            --   (μ ∘ second ε) ∘ id ∘ (second ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   (μ ∘ second ε) ∘ (second ε⁻¹ ∘ μ⁻¹)
            -- ≈⟨ assoc-middle ⟩
            --   μ ∘ (second ε ∘ second ε⁻¹) ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ second∘second) ⟩
            --   μ ∘ second (ε ∘ ε⁻¹) ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ʳ ε∘ε⁻¹)) ⟩
            --   μ ∘ second id ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id) ⟩
            --   μ ∘ id ∘ μ⁻¹
            -- ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
            --   μ ∘ μ⁻¹
            -- ≈⟨ μ∘μ⁻¹ ⟩
            --   id
            -- ≈⟨ sym≈ F-id ⟩
            --   Fₘ id
            -- ∎

         ; assocʳ∘assocˡ = {!!}

            -- begin
            --   Fₘ (assocʳ ∘ assocˡ)
            -- ≈⟨ F-∘ _ _ ⟩
            --   Fₘ assocʳ ∘ Fₘ assocˡ
            -- ≈⟨ ∘-resp-≈ F-assocʳ′ F-assocˡ′ ⟩
            --   (μ ∘ second μ ∘ assocʳ ∘ first μ⁻¹ ∘ μ⁻¹) ∘
            --   (μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹)
            -- ≈⟨ μ∘μ⁻¹
            --    ◎ g⁻¹∘g∘f (second⁻¹ μ∘μ⁻¹)
            --      ◎ g⁻¹∘g∘f assocʳ∘assocˡ
            --        ◎ g⁻¹∘g∘f (first⁻¹ μ⁻¹∘μ)
            --          ◎ g⁻¹∘g∘f μ⁻¹∘μ ⟩
            --   id
            -- ≈⟨ sym F-id ⟩
            --   Fₘ id
            -- ∎

         ; assocˡ∘assocʳ = {!!}

            -- begin
            --   Fₘ (assocˡ ∘ assocʳ)
            -- ≈⟨ F-∘ _ _ ⟩
            --   Fₘ assocˡ ∘ Fₘ assocʳ
            -- ≈⟨ ∘-resp-≈ F-assocˡ′ F-assocʳ′ ⟩
            --   (μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹) ∘
            --   (μ ∘ second μ ∘ assocʳ ∘ first μ⁻¹ ∘ μ⁻¹)
            -- ≈⟨ μ∘μ⁻¹
            --    ◎ g⁻¹∘g∘f (first⁻¹ μ∘μ⁻¹)
            --      ◎ g⁻¹∘g∘f assocˡ∘assocʳ
            --        ◎ g⁻¹∘g∘f (second⁻¹ μ⁻¹∘μ)
            --          ◎ g⁻¹∘g∘f μ⁻¹∘μ ⟩
            --   id
            -- ≈⟨ sym F-id ⟩
            --   Fₘ id
            -- ∎

         ; assocˡ∘⊗ = λ {a a′ b b′ c c′} {f g h} → 
            begin
              Fₘ (assocˡ ∘ (f ⊗ (g ⊗ h)))
            -- ≈⟨ F-∘ _ _ ⟩
            --   Fₘ assocˡ ∘ Fₘ (f ⊗ (g ⊗ h))
            -- ≈⟨ ∘-resp-≈ F-assocˡ′ (F-⊗′ _ _) ⟩
            --   (μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹) ∘
            --   (μ ∘ (Fₘ f ⊗ Fₘ (g ⊗ h)) ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ʳ {!!} ⟩
            --   (μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹) ∘
            --   (μ ∘ (Fₘ f ⊗ μ ∘ (Fₘ g ⊗ Fₘ h) ∘ μ⁻¹) ∘ μ⁻¹)
            -- ≈⟨ ∘-resp-≈ʳ {!!} ⟩
            --   (μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹) ∘
            --   (μ ∘ (Fₘ f ⊗ (μ ∘ (Fₘ g ⊗ Fₘ h) ∘ μ⁻¹)) ∘ μ⁻¹)
            -- ≈⟨ {!!} ⟩
            --   μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹ ∘
            --   μ ∘ (Fₘ f ⊗ (μ ∘ (Fₘ g ⊗ Fₘ h) ∘ μ⁻¹)) ∘ μ⁻¹
            -- ≈⟨ {!!} ⟩
            --   μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘
            --   (Fₘ f ⊗ (μ ∘ (Fₘ g ⊗ Fₘ h) ∘ μ⁻¹)) ∘ μ⁻¹
            -- ≈⟨ {!!} ⟩
            --   μ ∘ first μ ∘ assocˡ ∘ (Fₘ f ⊗ (Fₘ g ⊗ Fₘ h) ∘ μ⁻¹) ∘ μ⁻¹
            -- ≈⟨ {!!} ⟩
            --   μ ∘ first μ ∘ assocˡ ∘ ((Fₘ f ⊗ (Fₘ g ⊗ Fₘ h)) ∘ second μ⁻¹) ∘ μ⁻¹
            -- ≈⟨ {!!} ⟩
            --   μ ∘ first μ ∘ assocˡ ∘ (Fₘ f ⊗ (Fₘ g ⊗ Fₘ h)) ∘ second μ⁻¹ ∘ μ⁻¹
            ≈⟨ {!!} ⟩
              μ ∘ first μ ∘ ((Fₘ f ⊗ Fₘ g) ⊗ Fₘ h) ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
            ≈˘⟨ {!!} ⟩
              μ ∘ (μ ∘ (Fₘ f ⊗ Fₘ g) ⊗ Fₘ h) ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
            ≈˘⟨ {!!} ⟩
            --   μ ∘ (μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹ ⊗ Fₘ h) ∘
            --   first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
            -- ≈˘⟨ {!!} ⟩
            --   μ ∘ (μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹ ⊗ Fₘ h) ∘ μ⁻¹ ∘
            --   μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹
            -- ≈˘⟨ {!!} ⟩
            --   (μ ∘ (μ ∘ (Fₘ f ⊗ Fₘ g) ∘ μ⁻¹ ⊗ Fₘ h) ∘ μ⁻¹) ∘
            --   (μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹)
            -- ≈˘⟨ ∘-resp-≈ˡ (∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ˡ (F-⊗′ _ _)))) ⟩
            --   (μ ∘ (Fₘ (f ⊗ g) ⊗ Fₘ h) ∘ μ⁻¹) ∘
            --   (μ ∘ first μ ∘ assocˡ ∘ second μ⁻¹ ∘ μ⁻¹)
            -- ≈˘⟨ ∘-resp-≈ (F-⊗′ _ _) F-assocˡ′ ⟩
            --   Fₘ ((f ⊗ g) ⊗ h) ∘ Fₘ assocˡ
            -- ≈˘⟨ F-∘ _ _ ⟩
              Fₘ (((f ⊗ g) ⊗ h) ∘ assocˡ)
            ∎


         ; assocʳ∘⊗ = λ {a a′ b b′ c c′} {f g h} → {!!}

            -- begin
            --   Fₘ (assocʳ ∘ ((f ⊗ g) ⊗ h))
            -- ≈⟨ {!!} ⟩
            --   Fₘ ((f ⊗ (g ⊗ h)) ∘ assocʳ)
            -- ∎

         ; ⊗-resp-≈ = λ f≈h g≈k → {!!}

         }

    -- id⊗id : ∀ {a b : obj} → id {a = a} ⊗ id {a = b} ≈ id

    -- ∘⊗ : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : obj}
    --        {f : a₁ ⇨ a₂}{g : b₁ ⇨ b₂}
    --        {h : a₂ ⇨ a₃}{k : b₂ ⇨ b₃}
    --    → (h ⊗ k) ∘ (f ⊗ g) ≈ (h ∘ f) ⊗ (k ∘ g)

    -- unitorᵉˡ∘unitorⁱˡ : ∀ {a : obj} → unitorᵉˡ ∘ unitorⁱˡ {a = a} ≈ id
    -- unitorⁱˡ∘unitorᵉˡ : ∀ {a : obj} → unitorⁱˡ ∘ unitorᵉˡ {a = a} ≈ id

    -- unitorᵉʳ∘unitorⁱʳ : ∀ {a : obj} → unitorᵉʳ ∘ unitorⁱʳ {a = a} ≈ id
    -- unitorⁱʳ∘unitorᵉʳ : ∀ {a : obj} → unitorⁱʳ ∘ unitorᵉʳ {a = a} ≈ id

    -- assocʳ∘assocˡ : ∀ {a b c : obj} → assocʳ ∘ assocˡ ≈ id {a = a × (b × c)}
    -- assocˡ∘assocʳ : ∀ {a b c : obj} → assocˡ ∘ assocʳ ≈ id {a = (a × b) × c}

    -- assocˡ∘⊗ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
    --          → assocˡ ∘ (f ⊗ (g ⊗ h)) ≈ ((f ⊗ g) ⊗ h) ∘ assocˡ

    -- assocʳ∘⊗ : ∀ {a a′ b b′ c c′} {f : a ⇨ a′}{g : b ⇨ b′}{h : c ⇨ c′}
    --          → assocʳ ∘ ((f ⊗ g) ⊗ h) ≈ (f ⊗ (g ⊗ h)) ∘ assocʳ

    -- ⊗-resp-≈ : ∀ {f h : a ⇨ c} {g k : b ⇨ d} → f ≈ h → g ≈ k → f ⊗ g ≈ h ⊗ k

-}
