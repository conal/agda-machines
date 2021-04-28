{-# OPTIONS --safe --without-K #-}

module Categorical.Homomorphism where

open import Level using (Level; _⊔_)
import Relation.Binary.Construct.On as On

open import Categorical.Raw
-- For id-productsH. If Categorical.Laws gets slow to load, reconsider.
open import Categorical.Laws

open ≈-Reasoning

-- TODO: trim imports

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj obj₁ obj₂ : Set o
    a b c d e : obj
    a′ b′ c′ d′ e′ : obj

record Homomorphism
  {obj₁ : Set o₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁)
  {obj₂ : Set o₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  field
    Fₘ : (a ⇨₁ b) → (Fₒ a ⇨₂ Fₒ b)

open Homomorphism ⦃ … ⦄ public

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
  field
    F-id : Fₘ (id {_⇨_ = _⇨₁_}{a = a}) ≈ id
    F-∘  : ∀ (g : b ⇨₁ c) (f : a ⇨₁ b) → Fₘ (g ∘ f) ≈ Fₘ g ∘ Fₘ f

open CategoryH ⦃ … ⦄ public


record ProductsH
    {obj₁ : Set o₁} ⦃ _ : Products obj₁ ⦄ (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} ⦃ _ : Products obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ equiv₂ : Equivalent q _⇨₂′_ ⦄
    ⦃ cat₂ : Category _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    -- https://ncatlab.org/nlab/show/monoidal+functor
    ε : ⊤ ⇨₂ Fₒ ⊤
    μ : {a b : obj₁} → Fₒ a × Fₒ b ⇨₂ Fₒ (a × b)

    -- *Strong*
    ε⁻¹ : Fₒ ⊤ ⇨₂ ⊤
    μ⁻¹ : {a b : obj₁} → Fₒ (a × b) ⇨₂ Fₒ a × Fₒ b

    ε∘ε⁻¹ : ε ∘ ε⁻¹ ≈ id
    ε⁻¹∘ε : ε⁻¹ ∘ ε ≈ id

    μ∘μ⁻¹ : μ{a}{b} ∘ μ⁻¹ ≈ id
    μ⁻¹∘μ : μ⁻¹{a}{b} ∘ μ ≈ id

    -- TODO: Package as isomorphisms.

open ProductsH ⦃ … ⦄ public

id-productsH :
    {obj : Set o} ⦃ _ : Products obj ⦄ {_⇨₁_ : obj → obj → Set ℓ₁}
    {_⇨₂_ : obj → obj → Set ℓ₂}
    {q : Level} ⦃ equiv₂ : Equivalent q _⇨₂_ ⦄
    ⦃ cat₂ : Category _⇨₂_ ⦄
    ⦃ lawful-cat₂ : LawfulCategory _⇨₂_ q ⦄
    → ProductsH _⇨₁_ _⇨₂_ q ⦃ Hₒ = id-Hₒ ⦄
id-productsH = record { ε     = id
                      ; μ     = id
                      ; ε⁻¹   = id
                      ; μ⁻¹   = id
                      ; ε∘ε⁻¹ = identityˡ
                      ; ε⁻¹∘ε = identityˡ
                      ; μ∘μ⁻¹ = identityˡ
                      ; μ⁻¹∘μ = identityˡ
                      }

record MonoidalH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Products obj₁ ⦄ ⦃ _ : Monoidal _⇨₁′_ ⦄
    ⦃ _ : Products obj₂ ⦄ ⦃ _ : Monoidal _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ monoidal-categoryH ⦄ : CategoryH _⇨₁_ _⇨₂_ q

  field
    F-unitorᵉˡ : {a b : obj₁} → Fₘ unitorᵉˡ ∘ μ{a = ⊤}{a} ∘ first  ε ≈ unitorᵉˡ
    F-unitorⁱˡ : {a b : obj₁} → Fₘ unitorⁱˡ ≈ μ{a = ⊤}{a} ∘ first  ε ∘ unitorⁱˡ
    F-unitorᵉʳ : {a b : obj₁} → Fₘ unitorᵉʳ ∘ μ{a = a}{⊤} ∘ second ε ≈ unitorᵉʳ
    F-unitorⁱʳ : {a b : obj₁} → Fₘ unitorⁱʳ ≈ μ{a = a}{⊤} ∘ second ε ∘ unitorⁱʳ

    F-assocˡ : {a b c : obj₁} → 
      Fₘ assocˡ ∘ μ{a = a}{b × c} ∘ second μ ≈ μ ∘ first  μ ∘ assocˡ
    F-assocʳ : {a b c : obj₁} → 
      Fₘ assocʳ ∘ μ{a = a × b}{c} ∘ first  μ ≈ μ{a = a}{b × c} ∘ second μ ∘ assocʳ

    -- Are the next two properties theorems? I don't see them on nlab.
    F-! : Fₘ {_⇨₁_ = _⇨₁_}{a = a} ! ≈ ε ∘ !
    F-⊗ : ∀ (f : a ⇨₁ c)(g : b ⇨₁ d) → Fₘ (f ⊗ g) ∘ μ ≈ μ ∘ (Fₘ f ⊗ Fₘ g)

open MonoidalH ⦃ … ⦄ public


record BraidedH {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
                {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
                q ⦃ _ : Equivalent q _⇨₂′_ ⦄
                ⦃ _ : Products obj₁ ⦄ ⦃ _ : Braided _⇨₁′_ ⦄
                ⦃ _ : Products obj₂ ⦄ ⦃ _ : Braided _⇨₂′_ ⦄
                ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄
                ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ braided-monoidalH ⦄ : MonoidalH _⇨₁_ _⇨₂_ q
  field
    F-swap : {a b : obj₁} → Fₘ swap ∘ μ{a = a}{b} ≈ μ{a = b}{a} ∘ swap

open BraidedH ⦃ … ⦄ public

record CartesianH {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
                  {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
                  q ⦃ _ : Equivalent q _⇨₂′_ ⦄
                  ⦃ _ : Products obj₁ ⦄ ⦃ _ : Cartesian _⇨₁′_ ⦄
                  ⦃ _ : Products obj₂ ⦄ ⦃ _ : Cartesian _⇨₂′_ ⦄
                  ⦃ _ : Homomorphismₒ obj₁ obj₂ ⦄
                  ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄
                  ⦃ _ : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    ⦃ cartesian-braidedH ⦄ : BraidedH _⇨₁_ _⇨₂_ q
  field
    F-exl : {a b : obj₁} → Fₘ exl ∘ μ{a = a}{b} ≈ exl
    F-exr : {a b : obj₁} → Fₘ exr ∘ μ{a = a}{b} ≈ exr
    F-dup : {a b : obj₁} → Fₘ dup ≈ μ{a = a}{a} ∘ dup

open CartesianH ⦃ … ⦄ public


record BooleanH
    {obj₁ : Set o₁} ⦃ _ : Boolean obj₁ ⦄ (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} ⦃ _ : Boolean obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β : Bool ⇨₂ Fₒ Bool

open BooleanH ⦃ … ⦄ public

id-booleanH : {obj : Set o} ⦃ _ : Boolean obj ⦄
              {_⇨₁_ : obj → obj → Set ℓ₁} {_⇨₂_ : obj → obj → Set ℓ₂}
              ⦃ cat₂ : Category _⇨₂_ ⦄
            → BooleanH _⇨₁_ _⇨₂_ ⦃ Hₒ = id-Hₒ ⦄
id-booleanH = record { β = id }


record LogicH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    q ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Logic _⇨₁′_ ⦄
    ⦃ _ : Boolean obj₂ ⦄ ⦃ _ : Products obj₂ ⦄ ⦃ _ : Logic _⇨₂′_ ⦄
    ⦃ _ : Monoidal _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
    ⦃ pH : ProductsH _⇨₁′_ _⇨₂′_ q ⦄ ⦃ bH : BooleanH _⇨₁′_ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_

  field
    F-false : Fₘ false ∘ ε ≈ β ∘ false
    F-true  : Fₘ true  ∘ ε ≈ β ∘ true
    F-not   : Fₘ not   ∘ β ≈ β ∘ not
    F-∧     : Fₘ ∧   ∘ μ ∘ (β ⊗ β) ≈ β ∘ ∧
    F-∨     : Fₘ ∨   ∘ μ ∘ (β ⊗ β) ≈ β ∘ ∨
    F-xor   : Fₘ xor ∘ μ ∘ (β ⊗ β) ≈ β ∘ xor

open LogicH ⦃ … ⦄ public
