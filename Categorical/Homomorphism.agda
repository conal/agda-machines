{-# OPTIONS --safe --without-K #-}

module Categorical.Homomorphism where

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

open ≈-Reasoning

-- TODO: trim imports

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Homomorphismₒ (obj₁ : Set o₁) (obj₂ : Set o₂) : Set (o₁ ⊔ o₂) where
  field
    Fₒ : obj₁ → obj₂

id-Hₒ : Homomorphismₒ obj obj
id-Hₒ = record { Fₒ = id′ }

record Homomorphism
  {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  open Homomorphismₒ Hₒ public
  field
    Fₘ : (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

-- open Homomorphism ⦃ … ⦄ public  -- yes or no?

H-equiv : {obj₁ : Set o₁} {_⇨₁_ : obj₁ → obj₁ → Set ℓ₁}
          {obj₂ : Set o₂} {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
          {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
          ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
          (H : Homomorphism _⇨₁_ _⇨₂_)  -- note explicit/visible argument
        → Equivalent q _⇨₁_
H-equiv H = record { equiv = On.isEquivalence (Homomorphism.Fₘ H) equiv }

-- Category homomorphism (functor)
record CategoryH {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
                 {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
                 q ⦃ _ : Equivalent q _⇨₂_ ⦄
                 ⦃ _ : Category _⇨₁_ ⦄
                 ⦃ _ : Category _⇨₂_ ⦄
                 ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                 ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
       : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  open Homomorphism H public
  field
    F-id : Fₘ {a = a} id ≈ id
    F-∘  : ∀ (g : b ⇨₁ c) (f : a ⇨₁ b) → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f

-- open CategoryH ⦃ … ⦄ public

-- I don't know whether to open CategoryH and use it with instances or keep it
-- closed and open explicitly where used. I guess the main question is whether
-- we'll usually have a single special CategoryH instance per pairs of
-- categories or not. For now, keep it explicit, and see what we learn.

record MonoidalH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Monoidal _⇨₁′_ ⦄
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Monoidal _⇨₂′_ ⦄ -- ⦃ _ : LawfulMonoidal _⇨₂′_ q ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ -categoryH ⦄ : CategoryH _⇨₁_ _⇨₂_ q
  open CategoryH -categoryH public
  -- open Homomorphismₒ Hₒ

  field
    -- https://ncatlab.org/nlab/show/monoidal+functor
    ε : ⊤ ⇨₂ Fₒ ⊤
    μ : Fₒ a × Fₒ b ⇨₂ Fₒ (a × b)

    -- *Strong*
    ε⁻¹ : Fₒ ⊤ ⇨₂ ⊤
    μ⁻¹ : Fₒ (a × b) ⇨₂ Fₒ a × Fₒ b
    -- TODO: isomorphism properties. Package as isomorphism.

    F-unitorᵉˡ : Fₘ unitorᵉˡ ∘ μ{⊤}{a} ∘ first  ε ≈ unitorᵉˡ
    F-unitorⁱˡ : Fₘ unitorⁱˡ ≈ μ{⊤}{a} ∘ first  ε ∘ unitorⁱˡ
    F-unitorᵉʳ : Fₘ unitorᵉʳ ∘ μ{a}{⊤} ∘ second ε ≈ unitorᵉʳ
    F-unitorⁱʳ : Fₘ unitorⁱʳ ≈ μ{a}{⊤} ∘ second ε ∘ unitorⁱʳ

    F-assocˡ :
      Fₘ assocˡ ∘ μ{a}{b × c} ∘ second μ ≈ μ{a × b}{c} ∘ first  μ ∘ assocˡ
    F-assocʳ :
      Fₘ assocʳ ∘ μ{a × b}{c} ∘ first  μ ≈ μ{a}{b × c} ∘ second μ ∘ assocʳ

    -- Are the next two properties theorems? I don't see them on nlab.
    F-! : Fₘ {a} ! ≈ ε ∘ !
    F-⊗ : ∀ (f : a ⇨₁ c)(g : b ⇨₁ d) → Fₘ (f ⊗ g) ∘ μ ≈ μ ∘ (Fₘ f ⊗ Fₘ g)

{-

  -- The next two need ∘-resp-≈ and ⊗-resp-≈

  F-first : (f : a ⇨₁ c) → Fₘ (first f) ∘ μ{a}{b} ≈ μ{c}{b} ∘ first (Fₘ f)
  F-first f =
    begin
      Fₘ (first f) ∘ μ
    ≡⟨⟩
      Fₘ (f ⊗ id) ∘ μ
    ≈⟨ F-⊗ f id ⟩
      μ ∘ (Fₘ f ⊗ Fₘ id)
    ≈⟨ ∘-resp-≈ʳ (⊗-resp-≈ʳ F-id) ⟩
      μ ∘ (Fₘ f ⊗ id)
    ≡⟨⟩
      μ ∘ first (Fₘ f)
    ∎

  F-second : (g : b ⇨₁ d) → Fₘ (second g) ∘ μ{a}{b} ≈ μ{a}{d} ∘ second (Fₘ g)
  F-second g = 
    begin
      Fₘ (second g) ∘ μ
    ≡⟨⟩
      Fₘ (id ⊗ g) ∘ μ
    ≈⟨ F-⊗ id g ⟩
      μ ∘ (Fₘ id ⊗ Fₘ g)
    ≈⟨ ∘-resp-≈ʳ (⊗-resp-≈ˡ F-id) ⟩
      μ ∘ (id ⊗ Fₘ g)
    ≡⟨⟩
      μ ∘ second (Fₘ g)
    ∎

-}


record BraidedH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Braided _⇨₁′_ ⦄
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Braided _⇨₂′_ ⦄
    ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ monoidalH ⦄ : MonoidalH _⇨₁_ _⇨₂_ q
  open MonoidalH monoidalH public
  field
    F-swap : Fₘ swap ∘ μ{a}{b} ≈ μ{b}{a} ∘ swap

record CartesianH {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
                  {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
                  q ⦃ _ : Equivalent q _⇨₂′_ ⦄
                  ⦃ _ : Products obj₁ ⦄ ⦃ _ : Cartesian _⇨₁′_ ⦄
                  ⦃ _ : Products obj₂ ⦄ ⦃ _ : Cartesian _⇨₂′_ ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ braidedH ⦄ : BraidedH _⇨₁_ _⇨₂_ q
  open BraidedH braidedH public
  field
    F-exl : Fₘ exl ∘ μ{a}{b} ≈ exl
    F-exr : Fₘ exr ∘ μ{a}{b} ≈ exr
    F-dup : Fₘ dup ≈ μ{a}{a} ∘ dup


record BooleanH (obj₁ : Set o₁) (obj₂ : Set o₂)
    ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Boolean obj₂ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  : Set (o₁ ⊔ o₂) where
  open Homomorphismₒ Hₒ public
  field
    F-Bool : Fₒ Bool ≡ Bool
