{-# OPTIONS --safe --without-K #-}

-- Make lawfuls from lawfuls and homomorphisms

module Categorical.MakeLawful where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function using (_∘′_; const; _on_; flip) renaming (id to id′)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
  renaming (_×_ to _×′_)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidR
import Relation.Binary.Construct.On as On

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
                  {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
                  {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
                  ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Category _⇨₂_ ⦄
                  ⦃ _ : LawfulCategory _⇨₂_ q ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
                  (F : CategoryH _⇨₁_ _⇨₂_ q)
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
 where open CategoryH F


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
                  (F : MonoidalH _⇨₁_ _⇨₂_ q)
                → LawfulMonoidal _⇨₁_ q ⦃ equiv = H-equiv H ⦄
LawfulMonoidalᶠ ⦃ H = H ⦄ ⦃ pH = pH ⦄ ⦃ cH = cH ⦄ F = 
  let -- open Homomorphism H
      -- open ProductsH pH
      -- open CategoryH cH
      open MonoidalH F
  in record
  { id⊗id =
      begin
        Fₘ (id ⊗ id)
      ≈⟨ {!!} ⟩
        μ ∘ (Fₘ id ⊗ Fₘ id) ∘ μ⁻¹
      ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (⊗-resp-≈ F-id F-id)) ⟩
        μ ∘ (id ⊗ id) ∘ μ⁻¹
      ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ id⊗id) ⟩
        μ ∘ id ∘ μ⁻¹
      ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
        μ ∘ μ⁻¹
      ≈⟨ {!!} ⟩
        id
      ≈˘⟨ F-id ⟩
        Fₘ id
      ∎
  ; ∘⊗                = {!!}
  ; unitorᵉˡ∘unitorⁱˡ = {!!}
  ; unitorⁱˡ∘unitorᵉˡ = {!!}
  ; unitorᵉʳ∘unitorⁱʳ = {!!}
  ; unitorⁱʳ∘unitorᵉʳ = {!!}
  ; assocʳ∘assocˡ     = {!!}
  ; assocˡ∘assocʳ     = {!!}
  ; assocˡ∘⊗          = {!!}
  ; assocʳ∘⊗          = {!!}
  ; ⊗-resp-≈          = {!!}
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
